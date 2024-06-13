import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile

import Mathlib.Tactic.Common

namespace Regex.NFA

-- TODO: make this a claim about `Fin nfa.nodes.size`.
-- The issue is that `pathIn` uses Nat, and the conversion becomes non-trivial.
inductive εClosure (nfa : NFA) : Nat → Set Nat where
  | base : nfa.εClosure i i
  | step {i j k : Nat} (step : j ∈ nfa.εStep i) (rest : nfa.εClosure j k) :
    nfa.εClosure i k

-- theorem lt_of_εClosure_left {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i) :
--   i < nfa.nodes.size := by
--   cases h with
--   | base h => exact h
--   | step h => exact h

theorem lt_of_εClosure_right {nfa : NFA} {i j : Nat}
  (lt : i < nfa.nodes.size) (h : j ∈ nfa.εClosure i) :
  j < nfa.nodes.size := by
  induction h with
  | base => exact lt
  | @step i j _ step _ ih =>
    have : j < nfa.nodes.size := by
      simp [εStep] at step
      split at step <;> exact lt_of_εStep step
    exact ih this

theorem εClosure_snoc {nfa : NFA} (cls : j ∈ nfa.εClosure i) (step : k ∈ nfa.εStep j) :
  k ∈ nfa.εClosure i := by
  induction cls with
  | base => exact .step step .base
  | step step' _ ih => exact εClosure.step step' (ih step)

theorem εClosure_trans {nfa : NFA} (h₁ : j ∈ nfa.εClosure i) (h₂ : k ∈ nfa.εClosure j) :
  k ∈ nfa.εClosure i := by
  induction h₁ with
  | base => exact h₂
  | step head _ ih => exact .step head (ih h₂)

theorem subset_εClosure_of_mem {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i) :
  nfa.εClosure j ⊆ nfa.εClosure i := by
  intro k h'
  exact εClosure_trans h h'

-- Useful theorem when proving that reachability algorithm gives the εClosure
theorem mem_εStep_iff_εClosure_sub {nfa : NFA} {S : Set Nat} :
  (∀ i ∈ S, (_ : i < nfa.nodes.size) → ∀ j ∈ nfa[i].εStep, j ∈ S) ↔
  ∀ i ∈ S, nfa.εClosure i ⊆ S := by
  apply Iff.intro
  . intro assm i mem
    intro k cls
    induction cls with
    | base => exact mem
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [εStep, lt] at step
        exact ih (assm i mem lt j step)
      | isFalse nlt => simp [εStep, nlt] at step
  . intro assm i mem _ j step
    apply Set.mem_of_mem_of_subset _ (assm i mem)
    exact εClosure.step (εStep_of_εStep step) .base

/--
`nfa.reaches i cs` means that there is a path from the start node to `i` given by interleaving
ε closures and character steps, which corresponds to `cs`.
-/
inductive reaches (nfa : NFA) : Fin nfa.nodes.size → List Char → Prop where
  | nil (cls : i.val ∈ nfa.εClosure nfa.start) : nfa.reaches i []
  | snoc {i : Fin nfa.nodes.size} {j : Nat} {k : Fin nfa.nodes.size} {c : Char} {cs : List Char}
    (prev : reaches nfa i cs) (step : j ∈ nfa.charStep i c) (cls : k.val ∈ nfa.εClosure j) :
    nfa.reaches k (cs ++ [c])

end Regex.NFA
