import Regex.NFA.Compile
import RegexCorrectness.NFA.Order

namespace NFA

theorem pushRegex_get_lt (eq : pushRegex nfa next r = result) (i : Nat) (h : i < nfa.nodes.size) :
  result.val[i]'(Nat.lt_trans h result.property) = nfa[i] := by
  induction r generalizing nfa next with
  | empty | epsilon | char =>
    try apply pushRegex.empty eq
    try apply pushRegex.epsilon eq
    try apply pushRegex.char eq
    intro eq
    subst eq
    apply pushNode_get_lt i h
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ _ eq₃ _ eq₅ eq

    have h₁ : i < nfa₁.val.nodes.size := Nat.lt_trans h nfa₁.property
    have h₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h₁ nfa₂.property

    simp [eq, eq₅, pushNode_get_lt _ h₂]
    simp [ih₂ eq₃.symm h₁]
    simp [ih₁ eq₁.symm h]
  | concat r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    have h₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h nfa₂.property

    simp [eq, ih₁ eq₁.symm h₂, ih₂ eq₂.symm h]
  | star r ih =>
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      eq₁ eq₂ eq₃ eq₄ eq

    have ih := ih eq₂.symm (Nat.lt_trans h placeholder.property)

    conv =>
      lhs
      simp [eq, eq₄, get_eq_nodes_get, eq₃]

    have : i < compiled.val.nodes.size :=
      calc
        _ < _ := h
        _ < _ := placeholder.property
        _ < _ := compiled.property
    rw [Array.get_set (hj := this)]

    have : nfa.nodes.size ≠ i := Nat.ne_of_gt h
    simp [this, ←get_eq_nodes_get, ih, eq₁, pushNode_get_lt _ h]

theorem le_pushNode : nfa ≤ (pushNode nfa node h).val := by
  intro i
  have : i < (pushNode nfa node h).val.nodes.size := by
    simp
    exact Nat.lt_trans i.isLt (Nat.lt_succ_self _)
  exists this
  rw [pushNode_get_lt i i.isLt]

theorem le_pushRegex : nfa ≤ (pushRegex nfa next r).val := by
  induction r generalizing nfa next with
  | empty | epsilon | char _ => unfold pushRegex; exact le_pushNode
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate (rfl : pushRegex nfa next (.alternate r₁ r₂) = _)
    intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ _ eq₃ _ eq₅ eq
    rw [eq]

    calc
      _ ≤ nfa₁.val := eq₁ ▸ ih₁
      _ ≤ nfa₂.val := eq₃ ▸ ih₂
      _ ≤ nfa'.val := eq₅ ▸ le_pushNode
  | concat r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.concat (rfl : pushRegex nfa next (.concat r₁ r₂) = _)
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    rw [eq]

    calc
      _ ≤ nfa₂.val := eq₂ ▸ ih₂
      _ ≤ nfa₁.val := eq₁ ▸ ih₁
  | star r ih =>
    apply pushRegex.star (rfl : pushRegex nfa next (.star r) = _)
    intro placeholder compiled patched nfa' isLt inBounds property
      eq₁ eq₂ eq₃ eq₄ eq
    rw [eq]

    calc
      _ ≤ placeholder.val := eq₁ ▸ le_pushNode
      _ ≤ compiled.val := eq₂ ▸ ih
      _ ≤ nfa' := by
        intro i
        have : i < nfa'.nodes.size := by
          simp [eq₄, eq₃]
        exists this
        simp [eq₄, get_eq_nodes_get, eq₃]
        rw [Array.get_set]
        . split <;> try simp
          next eqi =>
            simp [←eqi, eq₂]
            rw [←get_eq_nodes_get, pushRegex_get_lt rfl _ placeholder.property]
            simp [eq₁]
        . exact i.isLt

theorem ge_pushRegex_start (eq : pushRegex nfa next r = result) :
  nfa.nodes.size ≤ result.val.start.val := by
  induction r generalizing nfa next with
  | empty =>
    apply pushRegex.empty eq
    intro eq
    subst eq
    simp
  | epsilon =>
    apply pushRegex.epsilon eq
    intro eq
    subst eq
    simp
  | char c =>
    apply pushRegex.char eq
    intro eq
    subst eq
    simp
  | alternate r₁ r₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ _ nfa₂ _ _ _ _ _ _ _ _ eq₅ eq
    rw [eq]
    simp
    rw [eq₅]
    simp [pushNode]
    exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
  | concat r₁ r₂ ih₁ =>
    apply pushRegex.concat eq
    intro nfa₂ nfa₁ _ _ eq₁ eq
    rw [eq]
    simp
    exact Nat.le_trans (Nat.le_of_lt nfa₂.property) (ih₁ eq₁.symm)
  | star r =>
    apply pushRegex.star eq
    intro _ _ _ nfa' _ _ _ _ _ _ eq₄ eq
    rw [eq]
    simp
    rw [eq₄]

theorem eq_or_ge_of_step_pushRegex {i j : Nat} (eq : pushRegex nfa next r = result)
  (h₁ : nfa.nodes.size ≤ i) (h₂ : i < result.val.nodes.size)
  (step : (∃ c, j ∈ result.val[i].charStep c) ∨ j ∈ result.val[i].εStep) :
  j = next ∨ nfa.nodes.size ≤ j := by
  induction r generalizing nfa next with
  | empty =>
    apply pushRegex.empty eq
    intro eq
    subst eq
    simp at h₂
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt h₁ h₂
    simp [this, NFA.Node.charStep, NFA.Node.εStep] at step
  | epsilon | char c =>
    try apply pushRegex.epsilon eq
    try apply pushRegex.char eq
    intro eq
    subst eq
    simp at h₂
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt h₁ h₂
    simp [this, NFA.Node.charStep, NFA.Node.εStep] at step
    exact .inl step
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ eq₂ eq₃ eq₄ eq₅ eq

    have get₂ (h : i < nfa₂.val.nodes.size) :
      result.val[i] = nfa₂.val[i] := by
      simp [eq, eq₅]
      rw [pushNode_get_lt _ h]

    have get₁ (h : i < nfa₁.val.nodes.size) :
      result.val[i] = nfa₁.val[i] := by
      rw [get₂ (Nat.lt_trans h nfa₂.property)]
      rw [pushRegex_get_lt eq₃.symm _ h]

    cases Nat.lt_or_ge i nfa₁.val.nodes.size with
    | inl lt =>
      apply ih₁ eq₁.symm h₁ lt
      exact get₁ lt ▸ step
    | inr ge =>
      cases Nat.lt_or_ge i nfa₂.val.nodes.size with
      | inl lt =>
        have ih₂ := ih₂ eq₃.symm ge lt (get₂ lt ▸ step)
        simp at ih₂
        cases ih₂ with
        | inl eq => exact .inl eq
        | inr ge => exact .inr (Nat.le_trans (Nat.le_of_lt nfa₁.property) ge)
      | inr ge =>
        simp [eq, eq₅] at h₂
        have : i = nfa₂.val.nodes.size := Nat.eq_of_ge_of_lt ge h₂
        simp [this, eq, eq₅, NFA.Node.charStep, NFA.Node.εStep] at step
        apply Or.inr
        cases step with
        | inl eq =>
          simp [eq, eq₂]
          exact ge_pushRegex_start eq₁.symm
        | inr eq =>
          simp [eq, eq₄]
          exact Nat.le_trans (Nat.le_of_lt nfa₁.property) (ge_pushRegex_start eq₃.symm)
  | concat r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    have get₂ (h : i < nfa₂.val.nodes.size) :
      result.val[i] = nfa₂.val[i] := by
      simp [eq]
      rw [pushRegex_get_lt eq₁.symm _ h]

    cases Nat.lt_or_ge i nfa₂.val.nodes.size with
    | inl lt =>
      apply ih₂ eq₂.symm h₁ lt
      exact get₂ lt ▸ step
    | inr ge =>
      simp [eq] at h₂ step
      have ih₁ := ih₁ eq₁.symm ge h₂ step
      apply Or.inr
      cases ih₁ with
      | inl eq =>
        simp [eq]
        exact ge_pushRegex_start eq₂.symm
      | inr ge => exact Nat.le_trans (Nat.le_of_lt nfa₂.property) ge
  | star r ih =>
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      eq₁ eq₂ eq₃ eq₄ eq

    cases Nat.lt_or_ge nfa.nodes.size i with
    | inl gt =>
      have lt : i < compiled.val.nodes.size := by
        simp [eq, eq₄, eq₃] at h₂
        exact h₂
      have : result.val[i] = compiled.val[i] := by
        simp [eq, eq₄, get_eq_nodes_get, eq₃]
        rw [Array.get_set_ne]
        simp
        exact Nat.ne_of_lt gt
      simp [this] at step
      have ih := ih eq₂.symm
      simp [eq₁] at ih
      have := ih gt lt step
      cases this with
      | inl eq => simp [eq]
      | inr ge => exact .inr (Nat.le_trans (Nat.le_succ _) ge)
    | inr le =>
      have : i = nfa.nodes.size := Nat.le_antisymm le h₁
      simp [this, eq, eq₄, get_eq_nodes_get] at step
      simp [eq₃] at step
      rw [Array.get_set_eq] at step
      simp [NFA.Node.charStep, NFA.Node.εStep] at step
      cases step with
      | inl eq =>
        have := ge_pushRegex_start eq₂.symm
        simp [eq₁] at this
        exact .inr (Nat.le_trans (Nat.le_succ _) (eq ▸ this))
      | inr eq => exact .inl eq

end NFA
