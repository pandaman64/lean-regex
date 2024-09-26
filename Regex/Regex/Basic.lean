import Regex.Syntax.Parser
import Regex.NFA
import Regex.VM

structure Regex where
  nfa : Regex.NFA
  maxTag : Nat := nfa.maxTag
deriving Repr

namespace Regex

def parse (s : String) : Except String Regex := do
  let expr ← Regex.Syntax.Parser.parse s
  let nfa := Regex.NFA.compile expr
  return { nfa := nfa }

def parse! (s : String) : Regex :=
  let nfa := Regex.NFA.compile (Regex.Syntax.Parser.parse! s)
  { nfa := nfa }

end Regex
