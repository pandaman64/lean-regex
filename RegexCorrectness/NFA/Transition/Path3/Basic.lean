import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Transition.Path

namespace Regex.NFA

-- Idea: what if we require at least one step? (Making this a non-reflexive transitive closure)
-- TODO: expand the motivation
inductive pathIn' (nfa : NFA) (lowerBound : Nat) : (first : Nat) → (last : Nat) → (cs : List Char) → Prop where
  | last (step : nfa.stepIn lowerBound i j cs) : nfa.pathIn' lowerBound i j cs
  | more {i j k : Nat} {cs₁ cs₂ : List Char}
    (step : nfa.stepIn lowerBound i j cs₁) (rest : nfa.pathIn' lowerBound j k cs₂) : nfa.pathIn' lowerBound i k (cs₁ ++ cs₂)

theorem pathIn'.le_left (path : pathIn' nfa lb i j cs) : lb ≤ i := by
  cases path with
  | last step => exact step.h₁
  | more step => exact step.h₁

theorem pathIn'.lt_left (path : pathIn' nfa lb i j cs) : i < nfa.nodes.size := by
  cases path with
  | last step => exact step.h₂
  | more step => exact step.h₂

theorem pathIn'.lt_right (path : pathIn' nfa lb i j cs) : j < nfa.nodes.size := by
  induction path with
  | last step => exact step.lt_right
  | more _ _ ih => exact ih

theorem pathIn'.castBound {nfa : NFA} {lb lb' : Nat}
  (le : lb' ≤ lb)
  (path : nfa.pathIn' lb i j cs) :
  nfa.pathIn' lb' i j cs := by
  induction path with
  | last step => exact .last (step.castStart le)
  | more step _ ih => exact .more (step.castStart le) ih

theorem pathIn'.cast {nfa nfa' : NFA} (lb : Nat)
  (eq : ∀ i, (h₁ : lb ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : pathIn' nfa lb i j cs) :
  pathIn' nfa' lb i j cs := by
  induction path with
  | last step =>
    have ⟨isLt, eq⟩ := eq _ step.h₁ step.h₂
    exact .last (step.cast isLt eq)
  | more step _ ih =>
    have ⟨isLt, eq⟩ := eq _ step.h₁ step.h₂
    exact .more (step.cast isLt eq) ih

theorem pathIn'.cast' {nfa nfa' : NFA} {lb : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : lb ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (path : pathIn' nfa' lb i j cs) :
  pathIn' nfa lb i j cs := by
  induction path with
  | last step => exact .last (step.cast assm (eq _ step.h₁ assm).symm)
  | more step _ ih =>
    have step' := step.cast assm (eq _ step.h₁ assm).symm
    have rest := ih step'.lt_right
    exact .more step' rest

theorem pathIn'.castLE {nfa : NFA} {lb lb' i i' : Nat}
  (assm : lb' ≤ i)
  (inBounds : ∀ i j, (h₁ : lb' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    lb ≤ j →
    lb' ≤ j)
  (path : pathIn' nfa lb i i' cs) :
  pathIn' nfa lb' i i' cs := by
  induction path with
  | last step => exact .last (step.castStart' assm)
  | @more i j k cs₁ cs₂ step rest ih =>
    have step' := step.castStart' assm
    have : lb' ≤ j := by
      cases step with
      | charStep _ h₂ step => exact inBounds i j assm h₂ (.inl ⟨_, step⟩) rest.le_left
      | εStep _ h₂ step => exact inBounds i j assm h₂ (.inr step) rest.le_left
    have rest' := ih this
    exact .more step' rest'

theorem pathIn'.snoc_char (path : pathIn' nfa lb i j cs) (assm : min lb k ≤ j)
  (step : k ∈ (nfa[j]'path.lt_right).charStep c)
  : pathIn' nfa (min lb k) i k (cs ++ [c]) := by
  induction path with
  | @last i j cs step' =>
    have step'' : nfa.stepIn (min lb k) j k [c] := .charStep assm step'.lt_right step
    exact .more (step'.castStart (Nat.min_le_left lb k)) (.last step'')
  | @more i j k cs₁ cs₂ step' _ ih =>
    simp
    exact .more (step'.castStart (Nat.min_le_left _ _)) (ih assm step)

theorem pathIn'.snoc_ε (path : pathIn' nfa lb i j cs) (assm : min lb k ≤ j)
  (step : k ∈ (nfa[j]'path.lt_right).εStep)
  : pathIn' nfa (min lb k) i k cs := by
  induction path with
  | @last i j cs step' =>
    suffices nfa.pathIn' (min lb k) i k (cs ++ []) by
      simp at this
      exact this
    have step'' : nfa.stepIn (min lb k) j k [] := .εStep assm step'.lt_right step
    exact .more (step'.castStart (Nat.min_le_left lb k)) (.last step'')
  | @more i j k cs₁ cs₂ step' _ ih =>
    exact .more (step'.castStart (Nat.min_le_left _ _)) (ih assm step)

theorem pathIn'.trans (path₁ : pathIn' nfa lb i j cs) (path₂ : pathIn' nfa lb j k cs') :
  pathIn' nfa lb i k (cs ++ cs') := by
  induction path₁ with
  | last step => exact .more step path₂
  | more step _ ih =>
    simp
    exact .more step (ih path₂)

end Regex.NFA
