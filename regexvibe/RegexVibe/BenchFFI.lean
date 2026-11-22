module

public import Regex
public import RegexVibe.VM.Refined

/-!
C ABI used by the Rust benchmarks in `/bench`.

The measured call is `regex_bench_count`: it only runs a match count. Parsing,
the flat-NFA conversion, and haystack clipping happen in `regex_bench_init`,
which is an `IO` action. The C caller keeps the resulting array and passes it
back into the pure counting function.

Engines, by the `engine` argument:

* `0` — `regex/pikevm`, the stock virtual machine (`Regex.count`)
* `1` — `regex/boundedrecursor`, the bounded backtracker
  (`useBacktracker := true`)
* `2` — `regexvibe/refinedpikevm`, the flat PikeVM

Haystacks are the curated rebar files under `bench/rebar/haystacks`, clipped so
a CPU simulator can finish them. Init checks that the three engines agree.
-/

open RegexVibe.VM.Refined (FlatNFA ofNFA layoutOk)

namespace RegexVibe.BenchFFI

/-- Stock PikeVM. -/
def enginePikeVm : UInt32 := 0
/-- Bounded backtracker (`Regex.Backtracker`). -/
def engineBoundedRecursor : UInt32 := 1
/-- Flat PikeVM in this package. -/
def engineRefinedPikeVm : UInt32 := 2

/-- Characters kept from each haystack. The rebar files are larger than a simulator wants. -/
def charLimit : Nat := 1024

structure Case where
  name : String
  pattern : String
  file : String
  /-- Drop this many lines (0-indexed, matching rebar) before clipping. -/
  lineStart : Nat := 0
  /-- Character budget. Short for the backtracker on alternation and the redos file. -/
  chars : Nat := charLimit

/--
Same tasks as `scripts/Bench.lean`, shortened to `charLimit` characters.
`sherlock-zh` starts at the line that contains the literal, which is far into
the file.
-/
def cases : Array Case := #[
  { name := "curated/literal/sherlock-en"
    pattern := "Sherlock Holmes"
    file := "opensubtitles/en-sampled.txt" },
  { name := "curated/literal/sherlock-casei-en"
    pattern := "(?i)Sherlock Holmes"
    file := "opensubtitles/en-sampled.txt" },
  { name := "curated/literal/sherlock-zh"
    pattern := "夏洛克·福尔摩斯"
    file := "opensubtitles/zh-sampled.txt"
    lineStart := 7480 },
  { name := "curated/literal-alternate/sherlock-en"
    pattern := "Sherlock Holmes|John Watson|Irene Adler|Inspector Lestrade|Professor Moriarty"
    file := "opensubtitles/en-sampled.txt"
    chars := 512 },
  { name := "curated/words/all-english"
    pattern := "\\b[0-9A-Za-z_]+\\b"
    file := "opensubtitles/en-sampled.txt" },
  { name := "curated/bounded-repeat/letters-en"
    pattern := "[A-Za-z]{8,13}"
    file := "opensubtitles/en-sampled.txt" },
  { name := "curated/cloud-flare-redos/simplified-long"
    pattern := ".*.*=.*"
    file := "cloud-flare-redos.txt"
    chars := 512 }
]

structure RefinedReady where
  nfa : Regex.NFA
  wf : nfa.WellFormed
  flat : FlatNFA
  hflat : ofNFA nfa = some flat
  info : Regex.OptimizationInfo
  hlayout : layoutOk nfa.size 2

structure Prepared where
  name : String
  pike : Regex
  refined : RefinedReady
  haystack : String
  hlen : haystack.utf8ByteSize + 1 < 2 ^ 64

/-- Keep the first `n` lines. `n` is exclusive. -/
partial def takeLines (s : String) (n : Nat) : String :=
  let rec go (p : String.Pos s) (seen : Nat) : String.Pos s :=
    if seen == n then p
    else if h : p ≠ s.endPos then
      let c := p.get h
      let p' := p.next h
      if c == '\n' then go p' (seen + 1) else go p' seen
    else
      s.endPos
  s.extract s.startPos (go s.startPos 0)

/-- Drop the first `n` lines. -/
partial def dropLines (s : String) (n : Nat) : String :=
  let rec go (p : String.Pos s) (seen : Nat) : String.Pos s :=
    if seen == n then p
    else if h : p ≠ s.endPos then
      let c := p.get h
      let p' := p.next h
      if c == '\n' then go p' (seen + 1) else go p' seen
    else
      s.endPos
  s.extract (go s.startPos 0) s.endPos

/-- Keep the first `n` characters, on a character boundary. -/
partial def takeChars (s : String) (n : Nat) : String :=
  let rec go (p : String.Pos s) (left : Nat) : String.Pos s :=
    if left == 0 then p
    else if h : p ≠ s.endPos then
      go (p.next h) (left - 1)
    else
      s.endPos
  s.extract s.startPos (go s.startPos n)

def clip (s : String) (lineStart chars : Nat) : String :=
  takeChars (dropLines s lineStart) chars

@[noinline]
def Prepared.run (p : Prepared) (engine : UInt32) : Nat :=
  if engine == enginePikeVm then
    p.pike.count p.haystack
  else if engine == engineBoundedRecursor then
    { p.pike with useBacktracker := true }.count p.haystack
  else
    RegexVibe.VM.Refined.count p.refined.nfa p.refined.wf p.refined.flat p.refined.hflat
      p.refined.info p.haystack p.refined.hlayout p.hlen

def prepare (dir : String) (case : Case) : IO Prepared := do
  let raw ← IO.FS.readFile s!"{dir}/{case.file}"
  let haystack := clip raw case.lineStart case.chars
  let pike ← ofExcept <|
    Regex.parse case.pattern |>.mapError (fun e => IO.userError s!"{case.name}: {e}")
  match hflat : ofNFA pike.nfa with
  | none => throw <| IO.userError s!"{case.name}: NFA does not fit in the flat encoding"
  | some flat =>
    if hlen : haystack.utf8ByteSize + 1 < 2 ^ 64 then
      if hlayout : layoutOk pike.nfa.size 2 then
        let prepared : Prepared := {
          name := case.name
          pike
          haystack
          hlen
          refined := {
            nfa := pike.nfa
            wf := pike.wf
            flat
            hflat
            info := pike.optimizationInfo
            hlayout
          }
        }
        let pikeCount := prepared.run enginePikeVm
        let backCount := prepared.run engineBoundedRecursor
        let refinedCount := prepared.run engineRefinedPikeVm
        if pikeCount == backCount && backCount == refinedCount then
          return prepared
        else
          throw <| IO.userError s!"{case.name}: count mismatch pike={pikeCount} bounded={backCount} refined={refinedCount}"
      else
        throw <| IO.userError s!"{case.name}: capture layout does not fit"
    else
      throw <| IO.userError s!"{case.name}: haystack does not fit in a capture word"

/--
Read the haystacks and compile every pattern.

The exported C function for this `IO` action drops the dummy world and returns
an `EIO` result. It consumes `dir`. The C caller keeps the array and
`lean_inc`s it before each pure call, which consumes that reference.
-/
@[export regex_bench_init, noinline]
def benchInit (dir : String) : IO (Array Prepared) := do
  let mut loaded : Array Prepared := #[]
  for case in cases do
    loaded := loaded.push (← prepare dir case)
  return loaded

@[export regex_bench_n_cases, noinline]
def benchNCases (loaded : Array Prepared) : UInt32 :=
  UInt32.ofNat loaded.size

/-- Match count for one prepared case. No `IO`: the caller passes the array from `benchInit`. -/
@[export regex_bench_count, noinline]
def benchCount (loaded : Array Prepared) (caseId engine : UInt32) : UInt64 :=
  match loaded[caseId.toNat]? with
  | some prepared => (prepared.run engine).toUInt64
  | none => 0

@[export regex_bench_case_name, noinline]
def benchCaseName (loaded : Array Prepared) (caseId : UInt32) : String :=
  match loaded[caseId.toNat]? with
  | some prepared => prepared.name
  | none => ""

end RegexVibe.BenchFFI
