import RegexCorrectness.NFA.Basic

namespace Regex.NFA

inductive stepIn (nfa : NFA) (lowerBound : Nat) : (current next : Nat) → (cs : List Char) → Prop where
  | charStep {i j : Nat} {c : Char} (h₁ : lowerBound ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c) : nfa.stepIn lowerBound i j [c]
  | εStep {i j : Nat} (h₁ : lowerBound ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].εStep) : nfa.stepIn lowerBound i j []

theorem stepIn.h₁ {nfa : NFA} {lb i j : Nat} {cs : List Char}
  (step : nfa.stepIn lb i j cs) : lb ≤ i := by
  cases step with
  | charStep h₁ _ _ => exact h₁
  | εStep h₁ _ _ => exact h₁

theorem stepIn.h₂ {nfa : NFA} {lb i j : Nat} {cs : List Char}
  (step : nfa.stepIn lb i j cs) : i < nfa.nodes.size := by
  cases step with
  | charStep _ h₂ _ => exact h₂
  | εStep _ h₂ _ => exact h₂

theorem stepIn.step {nfa : NFA} {lb i j : Nat} {cs : List Char}
  (step : nfa.stepIn lb i j cs) :
  (∃ c, j ∈ (nfa[i]'step.h₂).charStep c) ∨ j ∈ (nfa[i]'step.h₂).εStep := by
  cases step with
  | charStep _ _ step => exact .inl ⟨_, step⟩
  | εStep _ _ step => exact .inr step

theorem le_of_stepIn (step : stepIn nfa lb i j cs) : lb ≤ i := by
  cases step with
  | charStep h₁ => exact h₁
  | εStep h₁ => exact h₁

theorem stepIn.lt_right (step : stepIn nfa lb i j cs) : j < nfa.nodes.size := by
  match step.step with
  | .inl ⟨_, step⟩ => exact lt_of_charStep step
  | .inr step => exact lt_of_εStep step

theorem stepIn.castBound' {nfa : NFA} (le : lb' ≤ i) (step : stepIn nfa lb i j cs) :
  nfa.stepIn lb' i j cs := by
  cases step with
  | charStep h₁ h₂ step => exact .charStep le h₂ step
  | εStep h₁ h₂ step => exact .εStep le h₂ step

theorem stepIn.castBound {nfa : NFA} (le : lb' ≤ lb) (step : stepIn nfa lb i j cs) :
  nfa.stepIn lb' i j cs := step.castBound' (Nat.le_trans le step.h₁)

theorem stepIn.cast {nfa nfa' : NFA}
  (step : nfa.stepIn lb i j cs)
  (h : i < nfa'.nodes.size)
  (eq : nfa[i]'(step.h₂) = nfa'[i]) :
  nfa'.stepIn lb i j cs := by
  cases step with
  | charStep h₁ h₂ step =>
    exact .charStep h₁ h (eq ▸ step)
  | εStep h₁ h₂ step =>
    exact .εStep h₁ h (eq ▸ step)

theorem stepIn.nil_or_singleton (h : stepIn nfa lb i j cs) :
  cs = [] ∨ ∃ c, cs = [c] := by
  cases h with
  | εStep => exact .inl rfl
  | charStep => exact .inr ⟨_, rfl⟩

theorem stepIn.nil_of_snoc (h : stepIn nfa lb i j (cs ++ [c])) :
  cs = [] := by
  generalize h' : cs ++ [c] = cs' at h
  cases h with
  | εStep => simp at h'
  | charStep =>
    cases cs with
    | nil => rfl
    | cons _ _ =>
      have := congrArg List.length h'
      simp at this

/--

A predicate that represents a path in a NFA, with each starting node being at least `lowerBound`.

## Motivation

When we reason about an NFA constructed by `pushRegex nfa next r`, we are typically intersted in
paths that uses only the nodes added by `pushRegex` (and the last step to escape to `next`).
The definition of `pathIn` limits `first` to be at least `lowerBound` to capture this notion.

-/
inductive pathIn (nfa : NFA) (lowerBound : Nat) : (first : Nat) → (last : Nat) → (cs : List Char) → Prop where
  | last (step : nfa.stepIn lowerBound i j cs) : nfa.pathIn lowerBound i j cs
  | more {i j k : Nat} {cs₁ cs₂ : List Char}
    (step : nfa.stepIn lowerBound i j cs₁) (rest : nfa.pathIn lowerBound j k cs₂) : nfa.pathIn lowerBound i k (cs₁ ++ cs₂)

theorem pathIn.le_left (path : pathIn nfa lb i j cs) : lb ≤ i := by
  cases path with
  | last step => exact step.h₁
  | more step => exact step.h₁

theorem pathIn.lt_left (path : pathIn nfa lb i j cs) : i < nfa.nodes.size := by
  cases path with
  | last step => exact step.h₂
  | more step => exact step.h₂

theorem pathIn.lt_right (path : pathIn nfa lb i j cs) : j < nfa.nodes.size := by
  induction path with
  | last step => exact step.lt_right
  | more _ _ ih => exact ih

theorem pathIn.castBound {nfa : NFA} {lb lb' : Nat}
  (le : lb' ≤ lb)
  (path : nfa.pathIn lb i j cs) :
  nfa.pathIn lb' i j cs := by
  induction path with
  | last step => exact .last (step.castBound le)
  | more step _ ih => exact .more (step.castBound le) ih

theorem pathIn.cast {nfa nfa' : NFA} (lb : Nat)
  (eq : ∀ i, (h₁ : lb ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : pathIn nfa lb i j cs) :
  pathIn nfa' lb i j cs := by
  induction path with
  | last step =>
    have ⟨isLt, eq⟩ := eq _ step.h₁ step.h₂
    exact .last (step.cast isLt eq)
  | more step _ ih =>
    have ⟨isLt, eq⟩ := eq _ step.h₁ step.h₂
    exact .more (step.cast isLt eq) ih

theorem pathIn.cast' {nfa nfa' : NFA} {lb : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : lb ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (path : pathIn nfa' lb i j cs) :
  pathIn nfa lb i j cs := by
  induction path with
  | last step => exact .last (step.cast assm (eq _ step.h₁ assm).symm)
  | more step _ ih =>
    have step' := step.cast assm (eq _ step.h₁ assm).symm
    have rest := ih step'.lt_right
    exact .more step' rest

theorem pathIn.castLE {nfa : NFA} {lb lb' i i' : Nat}
  (assm : lb' ≤ i)
  (inBounds : ∀ i j, (h₁ : lb' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    lb ≤ j →
    lb' ≤ j)
  (path : pathIn nfa lb i i' cs) :
  pathIn nfa lb' i i' cs := by
  induction path with
  | last step => exact .last (step.castBound' assm)
  | @more i j k cs₁ cs₂ step rest ih =>
    have step' := step.castBound' assm
    have : lb' ≤ j := by
      cases step with
      | charStep _ h₂ step => exact inBounds i j assm h₂ (.inl ⟨_, step⟩) rest.le_left
      | εStep _ h₂ step => exact inBounds i j assm h₂ (.inr step) rest.le_left
    have rest' := ih this
    exact .more step' rest'

theorem pathIn.snoc_char (path : pathIn nfa lb i j cs) (assm : min lb k ≤ j)
  (step : k ∈ (nfa[j]'path.lt_right).charStep c)
  : pathIn nfa (min lb k) i k (cs ++ [c]) := by
  induction path with
  | @last i j cs step' =>
    have step'' : nfa.stepIn (min lb k) j k [c] := .charStep assm step'.lt_right step
    exact .more (step'.castBound (Nat.min_le_left lb k)) (.last step'')
  | @more i j k cs₁ cs₂ step' _ ih =>
    simp
    exact .more (step'.castBound (Nat.min_le_left _ _)) (ih assm step)

theorem pathIn.snoc_ε (path : pathIn nfa lb i j cs) (assm : min lb k ≤ j)
  (step : k ∈ (nfa[j]'path.lt_right).εStep)
  : pathIn nfa (min lb k) i k cs := by
  induction path with
  | @last i j cs step' =>
    suffices nfa.pathIn (min lb k) i k (cs ++ []) by
      simp at this
      exact this
    have step'' : nfa.stepIn (min lb k) j k [] := .εStep assm step'.lt_right step
    exact .more (step'.castBound (Nat.min_le_left lb k)) (.last step'')
  | @more i j k cs₁ cs₂ step' _ ih =>
    exact .more (step'.castBound (Nat.min_le_left _ _)) (ih assm step)

theorem pathIn.trans (path₁ : pathIn nfa lb i j cs) (path₂ : pathIn nfa lb j k cs') :
  pathIn nfa lb i k (cs ++ cs') := by
  induction path₁ with
  | last step => exact .more step path₂
  | more step _ ih =>
    simp
    exact .more step (ih path₂)

end Regex.NFA
