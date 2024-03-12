import Regex

def main (args : List String) : IO Unit := do
  let regex := args.get! 0
  let regex := Regex.Syntax.Parser.parse! regex
  let nfa := NFA.compile regex

  let file := args.get! 1
  let lines ← IO.FS.lines file
  let count ← lines.foldlM (fun acc line => do
    let line := line.trim
    if nfa.match line then
      return acc + 1
    else
      return acc
  ) 0
  IO.println s!"{count} lines matched"
