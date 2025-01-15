import Regex.Syntax.Parser
import Regex.NFA
import Regex.VM

structure Regex where
  nfa : Regex.NFA
  wf : nfa.WellFormed
  maxTag : Nat := nfa.maxTag
deriving Repr

namespace Regex

def parse (s : String) : Except Regex.Syntax.Parser.Error Regex := do
  let expr ← Regex.Syntax.Parser.parse s
  let nfa := Regex.NFA.compile expr
  return { nfa := nfa, wf := Regex.NFA.compile_wf }

def parse! (s : String) : Regex :=
  let nfa := Regex.NFA.compile (Regex.Syntax.Parser.parse! s)
  { nfa := nfa, wf := Regex.NFA.compile_wf }

end Regex
