import Regex.Syntax.Parser
import Regex.NFA
import Regex.VM

open String (Pos)

structure Regex where
  nfa : Regex.NFA
deriving Repr

namespace Regex

@[export lean_regex_regex_parse]
def parse (s : String) : Except String Regex := do
  let expr ← Regex.Syntax.Parser.parse s
  let nfa := Regex.NFA.compile expr
  return { nfa := nfa }

def parse! (s : String) : Regex :=
  let nfa := Regex.NFA.compile (Regex.Syntax.Parser.parse! s)
  { nfa := nfa }

structure Matches where
  regex : Regex
  heystack : String
  currentPos : Pos
deriving Repr

@[export lean_regex_regex_matches]
def _root_.Regex.matches (regex : Regex) (s : String) : Matches :=
  { regex := regex, heystack := s, currentPos := 0 }

@[export lean_regex_regex_matches_next]
def Matches.next? (self : Matches) : Option ((Pos × Pos) × Matches) := do
  let pos ← VM.searchNext self.regex.nfa ⟨self.heystack, self.currentPos⟩
  if self.currentPos < pos.2 then
    let next := { self with currentPos := pos.2 }
    pure (pos, next)
  else
    let next := { self with currentPos := self.heystack.next self.currentPos }
    pure (pos, next)

instance : Stream Matches (Pos × Pos) := ⟨Matches.next?⟩

end Regex
