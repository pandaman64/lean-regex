import Regex
import Regex.VM.Refined

open Regex.VM.Refined (FlatNFA)

def printUsage : IO Unit := do
  IO.println "Usage: bench -e <regex_pattern> [-n <iterations>] [-E vm|refined|both] <file_path>"
  IO.println "       bench --check"
  IO.println "Example: bench -e 'def' -n 1000 -E both ./file.lean"
  IO.println "Engines: vm (stock PikeVM), refined (flat NFA), both (default)"

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

def parseArgs (pattern : Option String) (iterations : Option Nat) (filePath : Option String)
    (engine : Engine) (check : Bool) (args : List String) : Except String Arguments :=
  match args with
  | "--check" :: args => parseArgs pattern iterations filePath engine true args
  | "-e" :: pattern :: args => parseArgs (some pattern) iterations filePath engine check args
  | "-E" :: name :: args => do
    let engine ← Engine.parse name
    parseArgs pattern iterations filePath engine check args
  | "-n" :: n :: args => do
    let n ← n.toNat?.getDM (throw "Iterations must be a number")
    if n < 0 then
      throw "Iterations must be a positive number"
    else
      parseArgs pattern (some n) filePath engine check args
  | filePath :: args => parseArgs pattern iterations (some filePath) engine check args
  | [] => do
    if check then
      return ⟨"", iterations.getD 1, "", engine, true⟩
    else
      let pattern ← pattern.getDM (throw "Pattern is required")
      let iterations := iterations.getD 1
      let filePath ← filePath.getDM (throw "File path is required")
      return ⟨pattern, iterations, filePath, engine, false⟩

unsafe def main (args : List String) : IO UInt32 := do
  match parseArgs .none .none .none .both false args with
  | .ok args =>
    if args.check then
      runSelfCheck
    else
      processFile args.pattern args.filePath args.iterations args.engine
      return 0
  | .error err =>
    IO.eprintln err
    printUsage
    return 1
