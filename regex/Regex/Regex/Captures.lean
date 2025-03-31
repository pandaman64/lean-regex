import Regex.Regex.Basic

open String (Pos)

namespace Regex

structure CapturedGroups where
  buffer : Array (Option Pos)
deriving Repr

def CapturedGroups.get (self : CapturedGroups) (index : Nat) : Option (Pos × Pos) := do
  let start ← (← self.buffer.get? (2 * index))
  let stop ← (← self.buffer.get? (2 * index + 1))
  return (start, stop)

def CapturedGroups.toArray (self : CapturedGroups) : Array (Option (Pos × Pos)) :=
  go 0 #[]
where
  go (i : Nat) (accum : Array (Option (Pos × Pos))) : Array (Option (Pos × Pos)) :=
    if 2 * i < self.buffer.size then
      go (i + 1) (accum.push (self.get i))
    else
      accum

structure Captures where
  regex : Regex
  haystack : String
  currentPos : Pos
deriving Repr

def Captures.next? (self : Captures) : Option (CapturedGroups × Captures) := do
  if self.currentPos ≤ self.haystack.endPos then
    let buffer ← VM.captureNextBuf self.regex.nfa self.regex.wf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩
    let groups := CapturedGroups.mk buffer.toArray
    let pos ← groups.get 0
    if self.currentPos < pos.2 then
      let next := { self with currentPos := pos.2 }
      pure (groups, next)
    else
      let next := { self with currentPos := self.haystack.next self.currentPos }
      pure (groups, next)
  else
    throw ()

def Captures.remaining (self : Captures) : Pos :=
  self.haystack.endPos + ⟨1⟩ - self.currentPos

theorem Captures.lt_next?_some {m : Captures} (h : m.next? = some (pos, m')) :
  m.currentPos.byteIdx < m'.currentPos.byteIdx := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some] at h
  have ⟨_, _, h⟩ := h
  have ⟨_, _, h⟩ := h
  split at h <;> simp at h
  next h' => simp [←h, h']
  next =>
    simp [←h, String.next]
    have : (m.haystack.get m.currentPos).utf8Size > 0 := Char.utf8Size_pos _
    omega

theorem Captures.haystack_eq_next?_some {m : Captures} (h : m.next? = some (pos, m')) :
  m'.haystack = m.haystack := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some] at h
  have ⟨_, _, h⟩ := h
  have ⟨_, _, h⟩ := h
  split at h <;> simp at h <;> simp [←h]

theorem Captures.next?_decreasing {m : Captures} (h : m.next? = some (pos, m')) :
  m'.remaining < m.remaining := by
  unfold remaining
  rw [haystack_eq_next?_some h]
  have h₁ : m.currentPos < m'.currentPos := lt_next?_some h
  have h₂ : m.currentPos < m.haystack.endPos + ⟨1⟩ := by
    simp [next?] at h
    split at h <;> try contradiction
    next le => exact Nat.add_le_add_right le 1
  exact Nat.sub_lt_sub_left h₂ h₁

theorem _root_.String.Pos.sizeOf_eq {p : Pos} : sizeOf p = 1 + p.byteIdx := rfl
theorem _root_.String.Pos.sizeOf_lt_iff {p p' : Pos} :
  sizeOf p < sizeOf p' ↔ p < p' := by
  simp [String.Pos.sizeOf_eq]

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  rw [String.Pos.sizeOf_lt_iff];
  exact Captures.next?_decreasing (by assumption))

instance : Stream Captures CapturedGroups := ⟨Captures.next?⟩

end Regex

def Regex.captures (regex : Regex) (s : String) : Captures :=
  { regex := regex, haystack := s, currentPos := 0 }
