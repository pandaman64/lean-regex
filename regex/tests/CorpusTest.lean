import Lake.Toml
import Lake.Toml.Decode
import Regex

open Lake (DecodeToml)
open Lake.Toml (Value DecodeError)
open String (Pos)

set_option autoImplicit false

deriving instance Repr for DecodeError

instance : ToString DecodeError where
  toString := reprStr

structure Span where
  start : Nat
  «end» : Nat
deriving Repr

def Span.eqv (s : Option Span) (p : Option (Pos × Pos)) : Bool :=
  match s, p with
  | .some s, .some p => s.start = p.1.byteIdx && s.end = p.2.byteIdx
  | .none, .none => true
  | .some _, .none => false
  | .none, .some _ => false

instance : DecodeToml Span where
  decode
    | .array _ #[start, «end»] => do
      let start : Nat ← DecodeToml.decode start
      let «end» : Nat ← DecodeToml.decode «end»
      return { start, «end» }
    | .table _ t => do
      let start ← t.decode `start
      let «end» ← t.decode `«end»
      return { start, «end» }
    | x => .error #[.mk x.ref "expected array of length 2 or table"]

structure Match where
  id : Nat
  spans : Array (Option Span)
deriving Repr

instance : ToString Match where
  toString := reprStr

def Match.eqv (m : Match) (positions : Array (Option (Pos × Pos))) : Bool :=
  m.spans.size = positions.size && ((m.spans.zip positions).all (fun (s, p) => Span.eqv s p))

def decodeSpans (vs : Array Value) : Except (Array DecodeError) (Array (Option Span)) :=
  vs.mapM fun v => match v with
    | .array _ #[] => pure .none
    | _ => DecodeToml.decode v |>.map .some

def decodeMatch (v : Value) : Except (Array DecodeError) Match := do
  match v with
  | .array _ spans =>
    try
      -- Try simple span format: [5, 12]
      let span : Span ← DecodeToml.decode v
      return { id := 0, spans := #[span] }
    catch _ =>
      -- Capture group spans format: [[5, 10], [6, 8], [], [9, 10]]
      let spans ← decodeSpans spans
      return { id := 0, spans }
  | .table _ t => do
    -- Table format with id and span/spans: { id = 5, span = [20, 21] } or { id = 5, spans = [[5, 10], [6, 8], [], [9, 10]] }
    let id ← t.decode `id
    match (←t.decode? (α := Span) `span) with
    | .some span => return { id, spans := #[span] }
    | .none =>
      let spans ← decodeSpans (←t.decode `spans)
      return { id, spans }
  | x => .error #[.mk x.ref "expected array or table"]

instance : DecodeToml Match := ⟨decodeMatch⟩

inductive Expr where
  | single : String → Expr
  | many : Array String → Expr
deriving Repr

instance : DecodeToml Expr where
  decode
    | .string _ s => return .single s
    | .array _ xs => return .many (←xs.mapM (DecodeToml.decode ·))
    | x => .error #[.mk x.ref "expected string or array of strings"]

inductive MatchKind where
  | all
  | leftmostFirst
  | leftmostLongest
deriving Repr, DecidableEq

instance : DecodeToml MatchKind where
  decode
    | .string ref s =>
      match s with
      | "all" => return .all
      | "leftmost-first" => return .leftmostFirst
      | "leftmost-longest" => return .leftmostLongest
      | _ => .error #[.mk ref "expected \"all\", \"leftmost\", or \"leftmost-longest\""]
    | x => .error #[.mk x.ref "expected string"]

inductive SearchKind where
  | earliest
  | leftmost
  | overlapping
deriving Repr, DecidableEq

instance : DecodeToml SearchKind where
  decode
    | .string ref s =>
      match s with
      | "earliest" => return .earliest
      | "leftmost" => return .leftmost
      | "overlapping" => return .overlapping
      | _ => .error #[.mk ref "expected \"earliest\", \"leftmost\", or \"overlapping\""]
    | x => .error #[.mk x.ref "expected string"]

structure RegexTest where
  group : String := ""
  name : String
  regex : Expr
  haystack : String
  «matches» : Array Match
  bounds : Option Span
  matchLimit : Option Nat
  compiles : Bool
  anchored : Bool
  caseInsensitive : Bool
  unescape : Bool
  unicode : Bool
  utf8 : Bool
  lineTerminator : String
  matchKind : MatchKind
  searchKind : SearchKind
deriving Repr

instance : ToString RegexTest where
  toString := reprStr

def decodeRegexTest (test : Lake.Toml.Value) : Except (Array DecodeError) RegexTest := do
  let table ← test.decodeTable
  let name ← table.decode `name
  let regex ← table.decode `regex
  let haystack ← table.decode `haystack
  let «matches» ← table.decode `matches
  let bounds ← table.decode? `bounds
  let matchLimit ← table.decode? `«match-limit»
  let compiles ← table.decode? `compiles
  let anchored ← table.decode? `anchored
  let caseInsensitive ← table.decode? `«case-insensitive»
  let unescape ← table.decode? `unescape
  let unicode ← table.decode? `unicode
  let utf8 ← table.decode? `utf8
  let lineTerminator ← table.decode? `«line-terminator»
  let matchKind ← table.decode? `«match-kind»
  let searchKind ← table.decode? `«search-kind»

  return {
    name,
    regex,
    haystack,
    «matches»,
    bounds,
    matchLimit,
    compiles := compiles.getD true,
    anchored := anchored.getD false,
    caseInsensitive := caseInsensitive.getD false,
    unescape := unescape.getD false,
    unicode := unicode.getD true,
    utf8 := utf8.getD true,
    lineTerminator := lineTerminator.getD "\n",
    matchKind := matchKind.getD .leftmostFirst,
    searchKind := searchKind.getD .leftmost
  }

instance : DecodeToml RegexTest := ⟨decodeRegexTest⟩

inductive TestResult where
  | ok
  | unsupported
deriving Repr

instance : ToString TestResult where
  toString
    | .ok => "ok"
    | .unsupported => "unsupported"

def decodeRegexTests (group : String) (toml : Lake.Toml.Table) : Except (Array DecodeError) (Array RegexTest) := do
  let tests : Array RegexTest ← toml.decode `test
  return tests.map fun test => { test with group }

def RegexTest.fullName (test : RegexTest) : String :=
  if test.group.isEmpty then
    test.name
  else
    s!"{test.group}/{test.name}"

def hasWordBoundary (s : String) : Bool :=
  let re := re! r##"\\b|\\B"##
  re.find s |>.isSome

def supported (test : RegexTest) : Bool :=
  test.bounds.isNone && !test.anchored && !test.caseInsensitive
  && !test.unescape && test.unicode && test.utf8
  && test.lineTerminator = "\n" && test.matchKind = .leftmostFirst && test.searchKind = .leftmost

def RegexTest.run (test : RegexTest) : Except String TestResult := do
  if not (supported test) then
    return .unsupported
  let regex ←
    match test.regex with
    | .single s =>
      if hasWordBoundary s then
        return .unsupported
      else
        match Regex.parse s, test.compiles with
        | .ok regex, true => pure regex
        | .ok _, false => throw s!"expected '{s}' to not compile, but it did"
        | .error e, true => throw s!"expected '{s}' to compile, but it did not: {e}"
        | .error _, false => return .ok
    | .many _ => return .unsupported
  let allCaptures := (regex.captureAll test.haystack).map (·.toArray)
  let captures :=
    match test.matchLimit with
    | .some limit => allCaptures.take limit
    | .none => allCaptures
  if test.matches.size != captures.size then
    throw s!"expected {test.matches}, got {captures}"
  else
    for (m, c) in test.matches.zip captures do
      if not (m.eqv c) then
        throw s!"expected {test.matches}, but got {captures}"
    return .ok

def getTomlOrThrow (toml : Except Lean.MessageLog Lake.Toml.Table) : IO Lake.Toml.Table := do
  match toml with
  | .ok toml => pure toml
  | .error e =>
    let errors ← e.toArray.mapM (fun m => m.toString)
    let message := String.join errors.toList
    throw (IO.Error.userError s!"Error loading TOML: {message}")

def load (filePath : String) : IO Lake.Toml.Table := do
  let tomlContent ← IO.FS.readFile filePath
  let fileMap := tomlContent.toFileMap
  let toml ← getTomlOrThrow (←(Lake.Toml.loadToml {
    input := tomlContent,
    fileName := filePath,
    fileMap := fileMap
  }).toIO')
  return toml

def loadTestCases (filePath : System.FilePath) : IO (Array RegexTest) := do
  let group := filePath.fileStem |>.getD ""
  let tomlContent ← IO.FS.readFile filePath
  let fileMap := tomlContent.toFileMap
  let toml ← getTomlOrThrow (←(Lake.Toml.loadToml {
    input := tomlContent,
    fileName := filePath.toString,
    fileMap := fileMap
  }).toIO')
  IO.ofExcept (decodeRegexTests group toml)

def main (args : List String) : IO UInt32 := do
  let files ← System.FilePath.readDir "tests/testdata"
  let tomlFiles := files
    |>.map (·.path)
    |>.filter (·.extension = some "toml")
    |>.qsort (fun a b => a.toString < b.toString)

  let tests ← tomlFiles.flatMapM (loadTestCases ·)
  let results := tests.map fun test => (test.fullName, test.run)

  -- Write results to CSV
  let mut csv := "test_name,result,error\n"
  for (name, result) in results do
    let row :=
      match result with
      | .ok result => s!"{name},{result},\n"
      | .error e => s!"{name},error,\"{e}\"\n"
    csv := csv ++ row

  if args.contains "--verify" then
    let actual ← IO.FS.readFile "tests/CorpusTest.csv"
    if actual = csv then
      return 0
    else
      IO.eprintln s!"CorpusTest.csv doesn't match. Expected:\n{csv}\n\nActual:\n{actual}"
      return 1
  else
    IO.println "Writing CorpusTest.csv"
    IO.FS.writeFile "tests/CorpusTest.csv" csv
    return 0
