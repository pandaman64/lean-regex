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

end NFA
