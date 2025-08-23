import RegexCorrectness.NFA.Semantics.ProofData.Basic

set_option autoImplicit false

namespace Regex.NFA

open Compile.ProofData in
theorem Step.eq_or_ge_of_pushRegex {nfa : NFA} {next e i it j it' update}
  (step : (nfa.pushRegex next e).Step nfa.nodes.size i it j it' update) :
  j = next ∨ nfa.nodes.size ≤ j := by
  induction e generalizing nfa next with
  | empty =>
    let pd := Empty.intro' nfa next
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = pd.nfa.nodes.size := Nat.eq_of_le_of_lt_succ step.ge lt
    exact absurd (this ▸ step) pd.not_step_start
  | epsilon =>
    let pd := Epsilon.intro' nfa next
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = nfa'.start := Nat.eq_of_le_of_lt_succ step.ge lt
    have := Epsilon.step_start_iff.mp (this ▸ step)
    simp [this]
    exact .inl rfl
  | anchor a =>
    let pd := Anchor.intro' nfa next a
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = nfa'.start := Nat.eq_of_le_of_lt_succ step.ge lt
    have := Anchor.step_start_iff.mp (this ▸ step)
    simp [this]
    exact .inl rfl
  | char c =>
    let pd := Char.intro' nfa next c
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = nfa'.start := Nat.eq_of_le_of_lt_succ step.ge lt
    have ⟨_, _, eq⟩ := Char.step_start_iff.mp (this ▸ step)
    simp [eq]
    exact .inl rfl
  | classes cs =>
    let pd := Classes.intro' nfa next cs
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = nfa'.start := Nat.eq_of_le_of_lt_succ step.ge lt
    have ⟨_, _, _, eq⟩ := Classes.step_start_iff.mp (this ▸ step)
    simp [eq]
    exact .inl rfl
  | group tag e ih =>
    let pd := Group.intro' nfa next tag e
    have step : (pd.nfa').Step nfa.nodes.size i it j it' update := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [Step.iff_save get] at step
      simp [step]
      exact .inl rfl
    next ne lt =>
      have step : Group.nfaExpr.Step Group.nfaClose.nodes.size i it j it' update :=
        (step.cast get).liftBound' (by simp [Group.nfaClose]; omega)
      have := ih step
      cases this with
      | inl eq => exact .inr (Nat.le_of_eq eq.symm)
      | inr le =>
        simp [Group.nfaClose] at le
        exact .inr (Nat.le_of_lt le)
    next =>
      simp [Step.iff_save get] at step
      simp [step]
      exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaClose_property) (ge_pushRegex_start rfl))
  | alternate e₁ e₂ ih₁ ih₂ =>
    let pd := Alternate.intro' nfa next e₁ e₂
    have step : (pd.nfa').Step nfa.nodes.size i it j it' update := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    simp [nlt] at get
    split_ifs at get
    next lt => exact ih₁ (step.cast get)
    next nlt lt =>
      have := ih₂ ((step.cast get).liftBound' (Nat.le_of_not_lt nlt))
      cases this with
      | inl eq => exact .inl eq
      | inr le => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₁_property) le)
    next =>
      simp [Step.iff_split get] at step
      cases step.2.1 with
      | inl eq₁ => exact .inr (eq₁ ▸ (ge_pushRegex_start rfl))
      | inr eq₂ =>
        have := ge_pushRegex_start (result := pd.nfa₂) rfl
        exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₁_property) (eq₂ ▸ this))
  | concat e₁ e₂ ih₁ ih₂ =>
    let pd := Concat.intro' nfa next e₁ e₂
    have step : (pd.nfa').Step nfa.nodes.size i it j it' update := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    split_ifs at get
    next lt => exact ih₂ (step.cast get)
    next nlt =>
      have := ih₁ (step.liftBound' (Nat.le_of_not_lt nlt))
      cases this with
      | inl eq => exact .inr (eq ▸ ge_pushRegex_start rfl)
      | inr le => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₂_property) le)
  | star greedy e ih =>
    let pd := Star.intro' nfa next greedy e
    have step : (pd.nfa').Step nfa.nodes.size i it j it' update := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [Step.iff_split get] at step
      cases step.2.1 with
      | inl eq =>
        split at eq
        . exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaPlaceholder_property) (eq ▸ ge_pushRegex_start rfl))
        . exact .inl eq
      | inr eq =>
        split at eq
        . exact .inl eq
        . exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaPlaceholder_property) (eq ▸ ge_pushRegex_start rfl))
    next ge' =>
      have ge : Star.nfaPlaceholder.nodes.size ≤ i := by
        simp [Star.nfaPlaceholder]
        omega
      have := ih ((step.cast get).liftBound' ge)
      simp [Star.nfaPlaceholder] at this
      cases this with
      | inl eq => exact .inr (eq ▸ Nat.le_refl _)
      | inr le => exact .inr (Nat.le_of_lt le)

theorem Path.eq_or_path_next {nfa : NFA} {next e result lb i it j it' update} (eq : nfa.pushRegex next e = result)
  (jlt : j < nfa.nodes.size) (ige : i ≥ nfa.nodes.size)
  (path : result.Path lb i it j it' update) :
  j = next ∨
  ∃ itm update₁ update₂,
    update = update₁ ++ update₂ ∧
    result.Path nfa.nodes.size i it next itm update₁ ∧
    result.Path lb next itm j it' update₂ := by
  induction path with
  | @last i it j it' update step =>
    have step := eq ▸ step.liftBound' ige
    have := step.eq_or_ge_of_pushRegex
    omega
  | @more i it j it' k it'' update updates step rest ih =>
    have step := step.liftBound' ige
    cases (eq ▸ step).eq_or_ge_of_pushRegex with
    | inl jeq =>
      simp [jeq] at *
      exact .inr ⟨it', List.ofOption update, updates, by simp, .last step, rest⟩
    | inr jge =>
      match ih jlt jge with
      | .inl keq => exact .inl keq
      | .inr ⟨itm, update₁, update₂, equ, path₁, path₂⟩ =>
        exact .inr ⟨itm, update ::ₒ update₁, update₂, by simp [equ], .more step path₁, path₂⟩

theorem Path.path_next_of_ne {nfa : NFA} {next e result lb i it j it' update} (eq : nfa.pushRegex next e = result)
  (jlt : j < nfa.nodes.size) (ige : i ≥ nfa.nodes.size) (ne : j ≠ next)
  (path : result.Path lb i it j it' update) :
  ∃ itm update₁ update₂,
    update = update₁ ++ update₂ ∧
    result.Path nfa.nodes.size i it next itm update₁ ∧
    result.Path lb next itm j it' update₂ := by
  have := path.eq_or_path_next eq jlt ige
  cases this with
  | inl eq => contradiction
  | inr h => exact h

end Regex.NFA
