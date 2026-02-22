/-
  Generate Simple_Case_Folding.txt from CaseFolding-original.txt

  Usage:
    lake exe GenSimpleCaseFolding [input_file] [output_file]

  Defaults:
    input_file  = data/CaseFolding-original.txt
    output_file = data/Simple_Case_Folding.txt

  This script extracts simple case folding mappings (status C and S)
  from the Unicode CaseFolding.txt file.
-/

def printUsage : IO Unit := do
  IO.println "Usage: GenSimpleCaseFolding [input_file] [output_file]"
  IO.println ""
  IO.println "Generates Simple_Case_Folding.txt from Unicode CaseFolding.txt"
  IO.println ""
  IO.println "Defaults:"
  IO.println "  input_file  = data/CaseFolding-original.txt"
  IO.println "  output_file = data/Simple_Case_Folding.txt"

structure CaseFoldEntry where
  codePoint : String
  mapping : String
  deriving Repr

def parseLine (line : String) : Option CaseFoldEntry := do
  -- Skip empty lines and comments
  let line := line.trimAscii.toString
  if line.isEmpty || line.startsWith "#" then
    none
  else
    -- Format: <code>; <status>; <mapping>; # <name>
    let parts := line.splitOn ";"
    if parts.length < 3 then
      none
    else
      let codePoint := parts[0]!.trimAscii.toString
      let status := parts[1]!.trimAscii.toString
      let mapping := parts[2]!.trimAscii.toString
      -- Only include C (common) and S (simple) status
      -- Exclude F (full) and T (Turkic)
      if status == "C" || status == "S" then
        some { codePoint, mapping }
      else
        none

def processFile (inputPath : String) (outputPath : String) : IO Unit := do
  let content ← IO.FS.readFile inputPath
  let lines := content.splitOn "\n"

  let entries := lines.filterMap parseLine

  let outputLines := entries.map fun e => s!"{e.codePoint};{e.mapping}"
  let output := String.intercalate "\n" outputLines ++ "\n"

  IO.FS.writeFile outputPath output
  IO.println s!"Generated {outputPath} with {entries.length} entries"

def main (args : List String) : IO UInt32 := do
  if args.contains "--help" || args.contains "-h" then
    printUsage
    return 0

  let inputPath := args.getD 0 "data/CaseFolding-original.txt"
  let outputPath := args.getD 1 "data/Simple_Case_Folding.txt"

  try
    processFile inputPath outputPath
    return 0
  catch e =>
    IO.eprintln s!"Error: {e}"
    return 1
