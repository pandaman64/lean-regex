import RegexCorrectness.NFA.Basic

namespace Regex.NFA

inductive stepIn (nfa : NFA) (start : Nat) : (current next : Nat) → (cs : List Char) → Prop where
  | charStep {i j : Nat} {c : Char} (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c) : nfa.stepIn start i j [c]
  | εStep {i j : Nat} (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].εStep) : nfa.stepIn start i j []

theorem stepIn.h₁ {nfa : NFA} {start : Nat} {i j : Nat} {cs : List Char}
  (step : nfa.stepIn start i j cs) : start ≤ i := by
  cases step with
  | charStep h₁ _ _ => exact h₁
  | εStep h₁ _ _ => exact h₁

theorem stepIn.h₂ {nfa : NFA} {start : Nat} {i j : Nat} {cs : List Char}
  (step : nfa.stepIn start i j cs) : i < nfa.nodes.size := by
  cases step with
  | charStep _ h₂ _ => exact h₂
  | εStep _ h₂ _ => exact h₂

theorem stepIn.step {nfa : NFA} {start : Nat} {i j : Nat} {cs : List Char}
  (step : nfa.stepIn start i j cs) :
  (∃ c, j ∈ (nfa[i]'step.h₂).charStep c) ∨ j ∈ (nfa[i]'step.h₂).εStep := by
  cases step with
  | charStep _ _ step => exact .inl ⟨_, step⟩
  | εStep _ _ step => exact .inr step

theorem le_of_stepIn {start} (step : stepIn nfa start i j cs) : start ≤ i := by
  cases step with
  | charStep h₁ => exact h₁
  | εStep h₁ => exact h₁

theorem stepIn.lt_right {start} (step : stepIn nfa start i j cs) : j < nfa.nodes.size := by
  match step.step with
  | .inl ⟨_, step⟩ => exact lt_of_charStep step
  | .inr step => exact lt_of_εStep step

theorem stepIn.castStart' {nfa : NFA} {start start' : Nat}
  (le : start' ≤ i) (step : stepIn nfa start i j cs) :
  nfa.stepIn start' i j cs := by
  cases step with
  | charStep h₁ h₂ step => exact .charStep le h₂ step
  | εStep h₁ h₂ step => exact .εStep le h₂ step

theorem stepIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start) (step : stepIn nfa start i j cs) :
  nfa.stepIn start' i j cs := step.castStart' (Nat.le_trans le step.h₁)

theorem stepIn.cast {nfa nfa' : NFA} {start : Nat}
  (step : nfa.stepIn start i j cs)
  (h : i < nfa'.nodes.size)
  (eq : nfa[i]'(step.h₂) = nfa'[i]) :
  nfa'.stepIn start i j cs := by
  cases step with
  | charStep h₁ h₂ step =>
    exact .charStep h₁ h (eq ▸ step)
  | εStep h₁ h₂ step =>
    exact .εStep h₁ h (eq ▸ step)

theorem stepIn.nil_or_singleton {start} (h : stepIn nfa start i j cs) :
  cs = [] ∨ ∃ c, cs = [c] := by
  cases h with
  | εStep => exact .inl rfl
  | charStep => exact .inr ⟨_, rfl⟩

theorem stepIn.nil_of_snoc {start} (h : stepIn nfa start i j (cs ++ [c])) :
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

end Regex.NFA
