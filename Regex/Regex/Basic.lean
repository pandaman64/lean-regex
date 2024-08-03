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
  haystack : String
  currentPos : Pos
deriving Repr

@[export lean_regex_regex_matches]
def _root_.Regex.matches (regex : Regex) (s : String) : Matches :=
  { regex := regex, haystack := s, currentPos := 0 }

@[export lean_regex_regex_matches_next]
def Matches.next? (self : Matches) : Option ((Pos × Pos) × Matches) := do
  if self.currentPos < self.haystack.endPos then
    let pos ← VM.searchNext self.regex.nfa ⟨self.haystack, self.currentPos⟩
    if self.currentPos < pos.2 then
      let next := { self with currentPos := pos.2 }
      pure (pos, next)
    else
      let next := { self with currentPos := self.haystack.next self.currentPos }
      pure (pos, next)
  else
    throw ()

def Matches.remaining (self : Matches) : Pos :=
  self.haystack.endPos - self.currentPos

theorem Matches.lt_next?_some {m : Matches} (h : m.next? = some (pos, m')) :
  m.currentPos < m'.currentPos := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some] at h
  have ⟨_, _, h⟩ := h
  split at h <;> simp at h
  next h' => simp [←h, h']
  next =>
    simp [←h, String.next]
    have : (m.haystack.get m.currentPos).utf8Size > 0 := Char.utf8Size_pos _
    omega

theorem Matches.next?_decreasing {m : Matches} (h : m.next? = some (pos, m')) :
  m'.remaining < m.remaining := by
  unfold remaining
  have : m'.haystack = m.haystack := by
    unfold next? at h
    split at h <;> simp [Option.bind_eq_some] at h
    have ⟨_, _, h⟩ := h
    split at h <;> simp at h <;> simp [←h]
  rw [this]
  have h₁ : m.currentPos < m'.currentPos := lt_next?_some h
  have h₂ : m.currentPos < m.haystack.endPos := by
    by_contra nlt
    simp [next?, nlt] at h
  exact Nat.sub_lt_sub_left h₂ h₁

theorem _root_.String.Pos.sizeOf_eq {p : Pos} : sizeOf p = 1 + p.byteIdx := rfl
theorem _root_.String.Pos.sizeOf_lt_iff {p p' : Pos} :
  sizeOf p < sizeOf p' ↔ p < p' := by
  simp [String.Pos.sizeOf_eq]
  omega

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  rw [String.Pos.sizeOf_lt_iff];
  exact Matches.next?_decreasing (by assumption))

instance : Stream Matches (Pos × Pos) := ⟨Matches.next?⟩

def find (regex : Regex) (haystack : String) : Option (Pos × Pos) :=
  regex.matches haystack |>.next? |>.map Prod.fst

def findAll (regex : Regex) (haystack : String) : Array (Pos × Pos) :=
  go (regex.matches haystack) #[]
where
  go (m : Matches) (accum : Array (Pos × Pos)) : Array (Pos × Pos) :=
    match _h : m.next? with
    | some (pos, m') => go m' (accum.push pos)
    | none => accum
  termination_by m.remaining

def replace (regex : Regex) (haystack : String) (replacement : String) : String :=
  match regex.find haystack with
  | some (startPos, endPos) =>
    haystack.extract 0 startPos ++ replacement ++ haystack.extract endPos haystack.endPos
  | none => haystack

def replaceAll (regex : Regex) (haystack : String) (replacement : String) : String :=
  go (regex.matches haystack) "" 0
where
  go (m : Matches) (accum : String) (endPos : Pos) : String :=
    match _h : m.next? with
    | some ((startPos', endPos'), m') =>
      go m' (accum ++ haystack.extract endPos startPos' ++ replacement) endPos'
    | none =>
      accum ++ haystack.extract endPos haystack.endPos
  termination_by m.remaining

end Regex
