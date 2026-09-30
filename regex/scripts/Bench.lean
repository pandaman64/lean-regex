import Regex
import Regex.VM.Refined

open Regex.VM.Refined (FlatNFA)

def printUsage : IO Unit := do
  IO.println "Usage: bench -e <regex_pattern> [-n <iterations>] [-E vm|refined|both] <file_path>"
  IO.println "       bench --check"
  IO.println "       bench --rebar [-n <iterations>] [-E vm|refined|both] [--rebar-dir <dir>]"
  IO.println "Example: bench -e 'def' -n 1000 -E both ./file.lean"
  IO.println "         bench --rebar -n 3"
  IO.println "Engines: vm (stock PikeVM), refined (flat NFA), both (default)"
  IO.println "rebar: a few tasks from https://github.com/BurntSushi/rebar (see bench/rebar/README.md)"

@[noinline]
def findCount (re : Regex) (content : String) : IO Nat :=
  re.count content |> pure

@[noinline]
unsafe def findCountRefined (flat : FlatNFA) (info : Regex.OptimizationInfo) (content : String) : IO Nat :=
  pure (Regex.VM.Refined.count flat info content)

def benchmark (name : String) (iterations : Nat) (step : IO Nat) : IO Nat := do
  let mut totalTime := 0
  let mut count := 0
  for _ in [:iterations] do
    let startTime ← IO.monoNanosNow
    count ← step
    let endTime ← IO.monoNanosNow
    totalTime := totalTime + (endTime - startTime)
  let totalTimeMs := totalTime.toFloat / 1_000_000
  IO.println s!"[{name}] Ran {iterations} iterations in {totalTimeMs}ms"
  IO.println s!"[{name}] Average time: {totalTimeMs / iterations.toFloat}ms per iteration"
  IO.println s!"[{name}] Found {count} matches"
  return count

unsafe def runSelfCheck : IO UInt32 := do
  let errors := Regex.VM.Refined.selfCheck
  if errors.isEmpty then
    IO.println "refined PikeVM matches the stock VM on the built-in cases"
    return 0
  else
    for err in errors do
      IO.eprintln err
    return 1

partial def readAll (stream : IO.FS.Stream) : IO String := do
  let mut buffer := ByteArray.empty
  while true do
    let data ← stream.read 8192
    if data.isEmpty then
      break
    buffer := buffer.append data
  return String.fromUTF8? buffer |>.getD ""

inductive Engine where
  | vm
  | refined
  | both
deriving Repr

def Engine.parse : String → Except String Engine
  | "vm" => .ok .vm
  | "refined" | "flat" => .ok .refined
  | "both" => .ok .both
  | other => .error s!"Unknown engine '{other}' (expected vm, refined, or both)"

unsafe def processFile (pattern : String) (filePath : String) (iterations : Nat) (engine : Engine) : IO Unit := do
  let content ←
    if filePath = "-" then
      readAll (← IO.getStdin)
    else
      IO.FS.readFile filePath
  let regex ← ofExcept $
    Regex.parse pattern |>.mapError (IO.userError s!"Regex parse error: {·}")
  let runVm : IO Nat := benchmark "vm" iterations (findCount regex content)
  let runRefined : IO Nat := do
    match Regex.VM.Refined.ofNFA regex.nfa with
    | none => throw (IO.userError "NFA does not fit in the flat UInt32 encoding")
    | some flat => benchmark "refined" iterations (findCountRefined flat regex.optimizationInfo content)
  match engine with
  | .vm => discard <| runVm
  | .refined => discard <| runRefined
  | .both =>
    let vmCount ← runVm
    let refinedCount ← runRefined
    if vmCount == refinedCount then
      IO.println s!"Match counts agree ({vmCount})"
    else
      throw (IO.userError s!"Match count mismatch: vm={vmCount} refined={refinedCount}")

structure Arguments where
  pattern : String
  iterations : Nat
  filePath : String
  engine : Engine
  check : Bool
  rebar : Bool
  rebarDir : String

/--
One curated rebar benchmark.

`source` is the definition file in BurntSushi/rebar. `lineEnd`, when set, is
rebar's exclusive line bound: lines are 0-indexed, and lines at or after
`lineEnd` are dropped. `expectCount` is rebar's published match count for the
`count` model. Benchmarks whose rebar model is `count-spans` leave it empty,
because that number is a sum of match lengths rather than a match count.
-/
structure RebarBench where
  name : String
  pattern : String
  haystack : String
  source : String
  lineEnd : Option Nat := none
  expectCount : Option Nat := none

/-
Selected from https://github.com/BurntSushi/rebar/tree/master/benchmarks/definitions/curated
Haystacks live under `bench/rebar/haystacks`. See `bench/rebar/README.md`.
-/
def rebarBenches : Array RebarBench := #[
  { name := "curated/literal/sherlock-en"
    pattern := "Sherlock Holmes"
    haystack := "opensubtitles/en-sampled.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/01-literal.toml"
    expectCount := some 513 },
  { name := "curated/literal/sherlock-casei-en"
    pattern := "(?i)Sherlock Holmes"
    haystack := "opensubtitles/en-sampled.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/01-literal.toml"
    expectCount := some 522 },
  { name := "curated/literal/sherlock-zh"
    pattern := "夏洛克·福尔摩斯"
    haystack := "opensubtitles/zh-sampled.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/01-literal.toml"
    expectCount := some 30 },
  { name := "curated/literal-alternate/sherlock-en"
    pattern := "Sherlock Holmes|John Watson|Irene Adler|Inspector Lestrade|Professor Moriarty"
    haystack := "opensubtitles/en-sampled.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/02-literal-alternate.toml"
    expectCount := some 714 },
  { name := "curated/words/all-english"
    pattern := "\\b[0-9A-Za-z_]+\\b"
    haystack := "opensubtitles/en-sampled.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/08-words.toml"
    lineEnd := some 2500 },
  { name := "curated/bounded-repeat/letters-en"
    pattern := "[A-Za-z]{8,13}"
    haystack := "opensubtitles/en-sampled.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/10-bounded-repeat.toml"
    lineEnd := some 5000
    expectCount := some 1833 },
  { name := "curated/cloud-flare-redos/simplified-long"
    pattern := ".*.*=.*"
    haystack := "cloud-flare-redos.txt"
    source := "https://github.com/BurntSushi/rebar/blob/master/benchmarks/definitions/curated/06-cloud-flare-redos.toml" }
]

/-- Keep the first `n` lines. `n` is exclusive, matching rebar's `line-end`. -/
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

unsafe def runRebar (dir : String) (iterations : Nat) (engine : Engine) : IO Unit := do
  IO.println "rebar curated benchmarks"
  IO.println "https://github.com/BurntSushi/rebar"
  IO.println "Definitions and haystacks are from that repository. See bench/rebar/README.md."
  for bench in rebarBenches do
    IO.println ""
    IO.println s!"--- {bench.name} ---"
    IO.println bench.source
    let path := s!"{dir}/{bench.haystack}"
    let raw ← IO.FS.readFile path
    let content :=
      match bench.lineEnd with
      | none => raw
      | some n => takeLines raw n
    let regex ← ofExcept $
      Regex.parse bench.pattern |>.mapError (IO.userError s!"Regex parse error in {bench.name}: {·}")
    let runVm : IO Nat := benchmark "vm" iterations (findCount regex content)
    let runRefined : IO Nat := do
      match Regex.VM.Refined.ofNFA regex.nfa with
      | none => throw (IO.userError s!"NFA does not fit in the flat UInt32 encoding ({bench.name})")
      | some flat => benchmark "refined" iterations (findCountRefined flat regex.optimizationInfo content)
    let count ←
      match engine with
      | .vm => runVm
      | .refined => runRefined
      | .both =>
        let vmCount ← runVm
        let refinedCount ← runRefined
        if vmCount == refinedCount then
          IO.println s!"Match counts agree ({vmCount})"
          pure vmCount
        else
          throw (IO.userError s!"Match count mismatch in {bench.name}: vm={vmCount} refined={refinedCount}")
    if let some expected := bench.expectCount then
      if count != expected then
        throw (IO.userError s!"{bench.name}: count {count} differs from rebar's published count {expected}")
      else
        IO.println s!"Count matches rebar's published count ({expected})"

def parseArgs (pattern : Option String) (iterations : Option Nat) (filePath : Option String)
    (engine : Engine) (check rebar : Bool) (rebarDir : String) (args : List String) :
    Except String Arguments :=
  match args with
  | "--check" :: args => parseArgs pattern iterations filePath engine true rebar rebarDir args
  | "--rebar" :: args => parseArgs pattern iterations filePath engine check true rebarDir args
  | "--rebar-dir" :: dir :: args => parseArgs pattern iterations filePath engine check rebar dir args
  | "-e" :: pattern :: args => parseArgs (some pattern) iterations filePath engine check rebar rebarDir args
  | "-E" :: name :: args => do
    let engine ← Engine.parse name
    parseArgs pattern iterations filePath engine check rebar rebarDir args
  | "-n" :: n :: args => do
    let n ← n.toNat?.getDM (throw "Iterations must be a number")
    if n < 0 then
      throw "Iterations must be a positive number"
    else
      parseArgs pattern (some n) filePath engine check rebar rebarDir args
  | filePath :: args => parseArgs pattern iterations (some filePath) engine check rebar rebarDir args
  | [] => do
    let iterations := iterations.getD 1
    if check || rebar then
      return ⟨pattern.getD "", iterations, filePath.getD "", engine, check, rebar, rebarDir⟩
    else
      let pattern ← pattern.getDM (throw "Pattern is required")
      let filePath ← filePath.getDM (throw "File path is required")
      return ⟨pattern, iterations, filePath, engine, false, false, rebarDir⟩

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs .none .none .none .both false false "bench/rebar/haystacks" args with
  | .ok args =>
    if args.check then
      let code ← runSelfCheck
      if code != 0 then
        return code
    if args.rebar then
      runRebar args.rebarDir args.iterations args.engine
    else if !args.check then
      processFile args.pattern args.filePath args.iterations args.engine
    return 0
  | .error err =>
    IO.eprintln err
    printUsage
    return 1
