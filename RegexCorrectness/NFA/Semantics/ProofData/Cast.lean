import RegexCorrectness.NFA.Semantics.ProofData.Basic

set_option autoImplicit false

namespace Regex.NFA

open Compile.ProofData in
theorem Step.eq_or_ge_of_pushRegex {nfa : NFA} {next e i span heap j span' heap'}
  (step : (nfa.pushRegex next e).val.Step nfa.nodes.size i span heap j span' heap') :
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
  | char c =>
    let pd := Char.intro' nfa next c
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = nfa'.start := Nat.eq_of_le_of_lt_succ step.ge lt
    have ⟨_, eq⟩ := Char.step_start_iff.mp (this ▸ step)
    simp [eq]
    exact .inl rfl
  | classes cs =>
    let pd := Classes.intro' nfa next cs
    have lt := step.lt
    simp [pushRegex] at lt
    have : i = nfa'.start := Nat.eq_of_le_of_lt_succ step.ge lt
    have ⟨_, _, eq⟩ := Classes.step_start_iff.mp (this ▸ step)
    simp [eq]
    exact .inl rfl
  | group tag e ih =>
    let pd := Group.intro' nfa next tag e
    have step : (pd.nfa').Step nfa.nodes.size i span heap j span' heap' := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [Step.iff_save get] at step
      simp [step]
      exact .inl rfl
    next ne lt =>
      have step : Group.nfaExpr.Step Group.nfaClose.nodes.size i span heap j span' heap' :=
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
    have step : (pd.nfa').Step nfa.nodes.size i span heap j span' heap' := step

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
        have := ge_pushRegex_start (result := ⟨Alternate.nfa₂, _⟩) rfl
        exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₁_property) (eq₂ ▸ this))
  | concat e₁ e₂ ih₁ ih₂ =>
    let pd := Concat.intro' nfa next e₁ e₂
    have step : (pd.nfa').Step nfa.nodes.size i span heap j span' heap' := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    split_ifs at get
    next lt => exact ih₂ (step.cast get)
    next nlt =>
      have := ih₁ (step.liftBound' (Nat.le_of_not_lt nlt))
      cases this with
      | inl eq => exact .inr (eq ▸ ge_pushRegex_start rfl)
      | inr le => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₂_property) le)
  | star e ih =>
    let pd := Star.intro' nfa next e
    have step : (pd.nfa').Step nfa.nodes.size i span heap j span' heap' := step

    have get := pd.get i step.lt
    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge step.ge
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [Step.iff_split get] at step
      cases step.2.1 with
      | inl eq => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaPlaceholder_property) (eq ▸ ge_pushRegex_start rfl))
      | inr eq => exact .inl eq
    next ge' =>
      have ge : Star.nfaPlaceholder.nodes.size ≤ i := by
        simp [Star.nfaPlaceholder]
        omega
      have := ih ((step.cast get).liftBound' ge)
      simp [Star.nfaPlaceholder] at this
      cases this with
      | inl eq => exact .inr (eq ▸ Nat.le_refl _)
      | inr le => exact .inr (Nat.le_of_lt le)

namespace Compile.ProofData

namespace Group

variable [Group] {span heap span' heap'}

theorem castFromExpr (path : nfaExpr.Path nfaClose.nodes.size nfaExpr.start span heap nfaClose.start span' heap') :
  nfa'.Path nfaClose.nodes.size nfaExpr.start span heap nfaClose.start span' heap' := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt_expr', (get_lt_expr lt).symm⟩

theorem castToExpr (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfaClose.nodes.size nfaExpr.start span heap nfaClose.start span' heap') :
  nfaExpr.Path nfaClose.nodes.size nfaExpr.start span heap nfaClose.start span' heap' := by
  have wf_expr := wf_expr wf next_lt
  apply path.cast' wf_expr.start_lt (Nat.le_of_lt size_lt_expr') wf_expr
  intro i _ lt
  exact get_lt_expr lt

end Group

namespace Alternate

variable [Alternate] {span heap span' heap'}

theorem castFrom₁ (path : nfa₁.Path nfa.nodes.size nfa₁.start span heap next span' heap') :
  nfa'.Path nfa.nodes.size nfa₁.start span heap next span' heap' := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt₁, (get_lt₁ lt).symm⟩

theorem castFrom₂ (path : nfa₂.Path nfa.nodes.size nfa₂.start span heap next span' heap') :
  nfa'.Path nfa.nodes.size nfa₂.start span heap next span' heap' := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt₂, (get_lt₂ lt).symm⟩

theorem castTo₁ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa₁.start span heap next span' heap') :
  nfa₁.Path nfa.nodes.size nfa₁.start span heap next span' heap' := by
  have wf₁ := wf₁ wf next_lt
  apply path.cast' wf₁.start_lt (Nat.le_of_lt size_lt₁) wf₁
  intro i _ lt
  exact get_lt₁ lt

theorem castTo₂ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa₁.nodes.size nfa₂.start span heap next span' heap') :
  nfa₂.Path nfa₁.nodes.size nfa₂.start span heap next span' heap' := by
  have wf₂ := wf₂ wf next_lt
  apply path.cast' wf₂.start_lt (Nat.le_of_lt size_lt₂) wf₂
  intro i _ lt
  exact get_lt₂ lt

end Alternate

namespace Concat

variable [Concat] {span heap span' heap'}

theorem castFrom₂ (path : nfa₂.Path nfa.nodes.size nfa₂.start span heap next span' heap') :
  nfa'.Path nfa.nodes.size nfa₂.start span heap next span' heap' := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size₂_lt, (get_lt₂ lt).symm⟩

theorem castTo₂ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa₂.start span heap next span' heap') :
  nfa₂.Path nfa.nodes.size nfa₂.start span heap next span' heap' := by
  have wf₂ := wf₂ wf next_lt
  apply path.cast' wf₂.start_lt (Nat.le_of_lt size₂_lt) wf₂
  intro i _ lt
  exact get_lt₂ lt

end Concat

namespace Star

variable [Star] {span heap span' heap'}

theorem castFromExpr (path : nfaExpr.Path nfaPlaceholder.nodes.size nfaExpr.start span heap nfaPlaceholder.start span' heap') :
  nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span heap nfaPlaceholder.start span' heap' := by
  apply path.cast
  intro i ge lt
  simp [nfaPlaceholder] at ge
  exact ⟨size_eq_expr' ▸ lt, (get_ne_start i (size_eq_expr' ▸ lt) (Nat.ne_of_gt ge)).symm⟩

theorem castToExpr (wf : nfa.WellFormed)
  (path : nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span heap nfaPlaceholder.start span' heap') :
  nfaExpr.Path nfaPlaceholder.nodes.size nfaExpr.start span heap nfaPlaceholder.start span' heap' := by
  have wf_expr := wf_expr wf
  apply path.cast' wf_expr.start_lt (Nat.le_of_eq size_eq_expr'.symm) wf_expr
  intro i ge lt
  simp [nfaPlaceholder] at ge
  exact (get_ne_start i (size_eq_expr' ▸ lt) (Nat.ne_of_gt ge))

end Star

end Compile.ProofData

end Regex.NFA
