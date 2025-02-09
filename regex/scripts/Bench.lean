import Regex

def printUsage : IO Unit := do
  IO.println "Usage: bench -e <regex_pattern> [-n <iterations>] <file_path>"
  IO.println "Example: bench -e 'def' -n 1000 ./file.lean"

def findCount (re : Regex) (content : String) : Nat :=
  re.findAll content |>.size

def benchmark (re : Regex) (content : String) (iterations : Nat) : IO Unit := do
  let mut totalTime := 0
  let mut count := 0
  for _ in [:iterations] do
    let startTime ← IO.monoNanosNow
    count := findCount re content
    let endTime ← IO.monoNanosNow
    totalTime := totalTime + (endTime - startTime)
  let totalTimeMs := totalTime.toFloat / 1_000_000
  IO.println s!"Ran {iterations} iterations in {totalTimeMs}ms"
  IO.println s!"Average time: {totalTimeMs / iterations.toFloat}ms per iteration"
  IO.println s!"Found {count} matches"

def processFile (pattern : String) (filePath : String) (iterations : Nat := 1) : IO Unit := do
  let content ← IO.FS.readFile filePath
  let regex ← ofExcept $
    Regex.parse pattern |>.mapError (IO.userError s!"Regex parse error: {·}")
  benchmark regex content iterations

structure Arguments where
  pattern : String
  iterations : Nat
  filePath : String

def parseArgs (pattern : Option String) (iterations : Option Nat) (filePath : Option String) (args : List String) : Except String Arguments :=
  match args with
  | "-e" :: pattern :: args => parseArgs (some pattern) iterations filePath args
  | "-n" :: n :: args => do
    let n ← n.toNat?.getDM (throw "Iterations must be a number")
    if n < 0 then
      throw "Iterations must be a positive number"
    else
      parseArgs pattern (some n) filePath args
  | filePath :: args => parseArgs pattern iterations (some filePath) args
  | [] => do
    let pattern ← pattern.getDM (throw "Pattern is required")
    let iterations := iterations.getD 1
    let filePath ← filePath.getDM (throw "File path is required")
    return ⟨pattern, iterations, filePath⟩

def main (args : List String) : IO UInt32 := do
  match parseArgs .none .none .none args with
  | .ok args =>
    processFile args.pattern args.filePath args.iterations
    return 0
  | .error err =>
    IO.eprintln err
    return 1
