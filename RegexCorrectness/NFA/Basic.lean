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

namespace NFAa

open NFA

def charStep (nfa : NFAa) (i : Nat) (c : Char) : Set Nat :=
  if h : i < nfa.nodes.size then
    nfa[i].charStep c
  else ∅

def εStep (nfa : NFAa) (i : Nat) : Set Nat :=
  if h : i < nfa.nodes.size then
    nfa[i].εStep
  else ∅

theorem lt_of_inBounds_of_charStep {node : Node} {j k : Nat} {c : Char}
  (inBounds : node.inBounds k) (mem : j ∈ node.charStep c) :
  j < k := by
  unfold Node.charStep at mem
  split at mem <;> try simp [Node.inBounds] at *
  simp [*]

theorem lt_of_inBounds_of_εStep {node : Node} {j k : Nat}
  (inBounds : node.inBounds k) (mem : j ∈ node.εStep) :
  j < k := by
  unfold Node.εStep at mem
  split at mem <;>
    try simp [Node.inBounds] at * <;>
    try cases mem <;>
    simp [*]

theorem lt_of_εStep {nfa : NFAa} {i j : Nat} {h : i < nfa.nodes.size}
  (mem : j ∈ nfa[i].εStep) : j < nfa.nodes.size := by
  have inBounds := nfa.inBounds ⟨i, h⟩
  simp [get_eq_nodes_get] at mem
  exact lt_of_inBounds_of_εStep inBounds mem

theorem lt_of_charStep {nfa : NFAa} {i j : Nat} {h : i < nfa.nodes.size}
  (mem : j ∈ nfa[i].charStep c) : j < nfa.nodes.size := by
  have inBounds := nfa.inBounds ⟨i, h⟩
  simp [get_eq_nodes_get] at mem
  exact lt_of_inBounds_of_charStep inBounds mem

-- def step (nfa : NFAa) (i : Fin nfa.nodes.size) (c : Option Char) : Set (Fin nfa.nodes.size) :=
--   match c, nfa[i], nfa.inBounds i with
--   | .some c, .char c' next, inBounds =>
--     if c == c' then {⟨next, Node.lt_of_inBounds.char inBounds⟩} else ∅
--   | .none, .epsilon next, inBounds => {⟨next, Node.lt_of_inBounds.epsilon inBounds⟩}
--   | .none, .split next₁ next₂, inBounds =>
--     have lt := Node.lt_of_inBounds.split inBounds
--     {⟨next₁, lt.left⟩, ⟨next₂, lt.right⟩}
--   | _, _, _ => ∅

-- theorem charStep_cases {nfa : NFAa} {i j : Fin nfa.nodes.size} {c : Char}
--   (h : j ∈ nfa.step i (.some c)) (char : nfa[i.val] = Node.char c j.val → motive)
--   : motive := by
--   simp [step] at h
--   split at h <;> try simp [*] at *
--   next c' c'' next _ eqn eqc _ =>
--     apply char
--     simp [eqn, eqc, h]

-- theorem εStep_cases {nfa : NFAa} {i j : Fin nfa.nodes.size}
--   (h : j ∈ nfa.step i .none)
--   (epsilon : nfa[i.val] = Node.epsilon j.val → motive)
--   (split : ∀ next₁ next₂, nfa[i.val] = Node.split next₁ next₂ → j.val = next₁ ∨ j.val = next₂ → motive) :
--   motive := by
--   simp [step] at h
--   split at h <;> try simp [*] at *
--   next next _ eqn _ _ =>
--     apply epsilon
--     simp [eqn, h]
--   next next₁ next₂ _ eqn _ _ =>
--     apply split next₁ next₂ eqn
--     cases h <;> simp [*]

-- theorem step_cases {nfa : NFAa} {i j : Fin nfa.nodes.size} (h : j ∈ nfa.step i c)
--   (char : ∀ c', c = .some c' → nfa[i.val] = Node.char c' j.val → motive)
--   (epsilon : c = none → nfa[i.val] = Node.epsilon j.val → motive)
--   (split : ∀ next₁ next₂, c = none → nfa[i.val] = Node.split next₁ next₂ →
--     j.val = next₁ ∨ j.val = next₂ → motive) :
--   motive := by
--   cases c with
--   | none => apply εStep_cases h (epsilon rfl) (fun next₁ next₂ => split _ _ rfl)
--   | some c' => apply charStep_cases h (char c' rfl)

end NFAa
