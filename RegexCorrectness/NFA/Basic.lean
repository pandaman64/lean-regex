import Regex.NFA.Basic

import Mathlib.Data.Set.Basic

namespace NFA

def Node.charStep (n : Node) (c : Char) : Set Nat :=
  match n with
  | Node.char c' next => if c == c' then {next} else ∅
  | _ => ∅

def Node.εStep (n : Node) : Set Nat :=
  match n with
  | Node.epsilon next => {next}
  | Node.split next₁ next₂ => {next₁, next₂}
  | _ => ∅

theorem lt_of_inBounds_of_charStep {nfa : NFA} {i j : Nat} {c : Char} {h : i < nfa.nodes.size}
  (inBounds : nfa.inBounds) (mem : j ∈ nfa[i].charStep c) :
  j < nfa.nodes.size := by
  unfold Node.charStep at mem
  split at mem <;> try contradiction
  next next eq =>
    split at mem <;> try contradiction
    simp at mem
    rw [mem]
    have := inBounds ⟨i, h⟩
    simp [eq, Node.inBounds] at this
    exact this

theorem lt_of_inBounds_of_εStep {nfa : NFA} {i j : Nat} {h : i < nfa.nodes.size}
  (inBounds : nfa.inBounds) (mem : j ∈ nfa[i].εStep) :
  j < nfa.nodes.size := by
  unfold Node.εStep at mem
  split at mem <;> try contradiction
  next next eq =>
    have := inBounds ⟨i, h⟩
    simp [eq, Node.inBounds] at this
    simp at mem
    rw [mem]
    exact this
  next next₁ next₂ eq =>
    have := inBounds ⟨i, h⟩
    simp [eq, Node.inBounds] at this
    simp at mem
    cases mem with
    | inl eq₁ =>
      rw [eq₁]
      exact this.left
    | inr eq₂ =>
      rw [eq₂]
      exact this.right

-- def Node.inBounds (n : Node) (size : Nat) : Prop :=
--   (∀ c, n.charStep c ⊆ { j | j < size }) ∧ n.εStep ⊆ { j | j < size }

-- @[simp]
-- theorem Node.inBounds.done {size : Nat} : Node.done.inBounds size := by
--   simp [inBounds, charStep, εStep]

-- @[simp]
-- theorem Node.inBounds.fail {size : Nat} : Node.fail.inBounds size := by
--   simp [inBounds, charStep, εStep]

-- @[simp]
-- theorem Node.inBounds.epsilon {size next : Nat} (h : next < size) :
--   (Node.epsilon next).inBounds size := by
--   simp [inBounds, charStep, εStep, h]

-- @[simp]
-- theorem Node.inBounds.char {size next : Nat} {c : Char} (h : next < size) :
--   (Node.char c next).inBounds size := by
--   simp [inBounds, charStep, εStep]
--   intro c'
--   split <;> simp [h]

-- @[simp]
-- theorem Node.inBounds.split {size next₁ next₂ : Nat} (h₁ : next₁ < size) (h₂ : next₂ < size) :
--   (Node.split next₁ next₂).inBounds size := by
--   simp [inBounds, charStep, εStep]
--   apply Set.insert_subset <;> simp [h₁, h₂]

-- theorem Node.inBounds_of_inBounds_of_le {n : Node} (h : n.inBounds size) (le : size ≤ size') :
--   n.inBounds size' := by
--   simp [inBounds] at *
--   apply And.intro
--   . intro c
--     apply le_trans (h.left c)
--     simp
--     intro j h
--     exact Nat.lt_of_lt_of_le h le
--   . apply le_trans h.right
--     simp
--     intro j h
--     exact Nat.lt_of_lt_of_le h le

-- def NFA.inBounds (nfa : NFA) :=
--   ∀ i : Fin nfa.nodes.size, nfa[i].inBounds nfa.nodes.size

end NFA
