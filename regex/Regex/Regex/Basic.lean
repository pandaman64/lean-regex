import Regex.Syntax.Parser
import Regex.NFA
import Regex.VM
import Regex.Backtracker

open String (Pos Iterator)

structure Regex where
  nfa : Regex.NFA
  wf : nfa.WellFormed
  maxTag : Nat := nfa.maxTag
  useBacktracker : Bool := false
deriving Repr

namespace Regex

def captureNextBuf (self : Regex) (bufferSize : Nat) (it : Iterator) : Option (Buffer bufferSize) :=
  if self.useBacktracker then
    Backtracker.captureNextBuf self.nfa self.wf bufferSize it
  else
    VM.captureNextBuf self.nfa self.wf bufferSize it

def searchNext (self : Regex) (it : Iterator) : Option (Pos × Pos) := do
  if self.useBacktracker then
    Backtracker.searchNext self.nfa self.wf it
  else
    VM.searchNext self.nfa self.wf it

def parse (s : String) : Except Regex.Syntax.Parser.Error Regex := do
  let expr ← Regex.Syntax.Parser.parse s
  let nfa := Regex.NFA.compile expr
  return { nfa := nfa, wf := Regex.NFA.compile_wf }

def parse! (s : String) : Regex :=
  let nfa := Regex.NFA.compile (Regex.Syntax.Parser.parse! s)
  { nfa := nfa, wf := Regex.NFA.compile_wf }

end Regex
