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
  stop : Nat
deriving Repr

def Span.eqv (s : Option Span) (p : Option (Pos × Pos)) : Bool :=
  match s, p with
  | .some s, .some p => s.start = p.1.byteIdx && s.stop = p.2.byteIdx
  | .none, .none => true
  | .some _, .none => false
  | .none, .some _ => false

instance : DecodeToml Span where
  decode
    | .array _ #[start, stop] => do
      let start : Nat ← DecodeToml.decode start
      let stop : Nat ← DecodeToml.decode stop
      return { start, stop }
    | x => .error #[.mk x.ref "expected array of length 2"]

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

structure RegexTest where
  group : String := ""
  name : String
  regex : String
  haystack : String
  «matches» : Array Match
--   matchLimit : Option Nat
--   compiles : Bool
--   anchored : Bool
--   caseInsensitive : Bool
--   unescape : Bool
--   unicode : Bool
--   utf8 : Bool
--   lineTerminator : Char
--   matchKind : String
--   searchKind : String
deriving Repr

instance : ToString RegexTest where
  toString := reprStr

def decodeRegexTest (test : Lake.Toml.Value) : Except (Array DecodeError) RegexTest := do
  let table ← test.decodeTable
  let name ← table.decode `name
  let regex ← table.decode `regex
  let haystack ← table.decode `haystack
  let «matches» ← table.decode `matches

  return {
    name,
    regex,
    haystack,
    «matches»,
  }

instance : DecodeToml RegexTest := ⟨decodeRegexTest⟩

def decodeRegexTests (group : String) (toml : Lake.Toml.Table) : Except (Array DecodeError) (Array RegexTest) := do
  let tests : Array RegexTest ← toml.decode `test
  return tests.map fun test => { test with group }

def RegexTest.fullName (test : RegexTest) : String :=
  if test.group.isEmpty then
    test.name
  else
    s!"{test.group}/{test.name}"

def RegexTest.run (test : RegexTest) : Except String Bool := do
  let regex ← Regex.parse test.regex |>.mapError toString
  let captures := (regex.captureAll test.haystack).map (·.toArray)
  if test.matches.size != captures.size then
    return false
  else
    return test.matches.zip captures |>.all fun (m, c) => m.eqv c

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

def main : IO Unit := do
  let files ← System.FilePath.readDir "tests/testdata"
  let tomlFiles := files.filter (·.path.extension = some "toml")
  let mut tests := #[]
  for file in tomlFiles do
    tests := tests ++ (←loadTestCases file.path)
  let mut results := #[]
  for test in tests do
    let result ← IO.ofExcept test.run
    results := results.push (test.fullName, result)

  -- Write results to CSV
  let mut csv := "test_name,result\n"
  for (name, result) in results do
    csv := csv ++ s!"{name},{result}\n"

  IO.FS.writeFile "empty_results.csv" csv
  return ()
