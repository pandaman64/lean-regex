import Regex.NFA
import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile.ProofData

import Mathlib.Tactic.Common

namespace Regex.NFA

theorem pushRegex_get_lt (eq : pushRegex nfa next r = result) (i : Nat) (h : i < nfa.nodes.size) :
  result.val[i]'(Nat.lt_trans h result.property) = nfa[i] := by
  induction r generalizing nfa next with
  | empty | epsilon | char | classes =>
    try apply pushRegex.empty eq
    try apply pushRegex.epsilon eq
    try apply pushRegex.char eq
    try apply pushRegex.sparse eq
    intro eq
    subst eq
    apply pushNode_get_lt i h
  | group _ r ih =>
    apply pushRegex.group eq
    intro nfa' nfa'' nfa''' property eq₁ eq₂ eq₃ eq

    have h₁ : i < nfa'.val.nodes.size := Nat.lt_trans h nfa'.property
    have h₂ : i < nfa''.val.nodes.size := Nat.lt_trans h₁ nfa''.property

    simp [eq, eq₃, pushNode_get_lt _ h₂]
    simp [ih eq₂.symm h₁]
    simp [eq₁, pushNode_get_lt _ h]
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq

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
    intro placeholder compiled patched nfa' property
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

open Compile.ProofData in
theorem ge_pushRegex_start (eq : pushRegex nfa next r = result) :
  nfa.nodes.size ≤ result.val.start := by
  induction r generalizing nfa next with
  | empty =>
    have data := Empty.intro eq
    rw [←eq, data.eq]
    simp [data.start_eq]
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
  | classes c =>
    apply pushRegex.sparse eq
    intro eq
    subst eq
    simp
  | group =>
    apply pushRegex.group eq
    intro nfa' nfa'' nfa''' property _ _ eq₃ eq
    rw [eq]
    simp
    rw [eq₃]
    simp
    apply Nat.le_of_lt (Nat.lt_trans nfa'.property nfa''.property)
  | alternate r₁ r₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ _ nfa₂ _ _ _ _ _ _ _ eq₅ eq
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
    intro _ _ _ nfa' _ _ _ _ eq₄ eq
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
    have : i = nfa.nodes.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, NFA.Node.charStep, NFA.Node.εStep] at step
  | epsilon | char c | classes r =>
    try apply pushRegex.epsilon eq
    try apply pushRegex.char eq
    try apply pushRegex.sparse eq
    intro eq
    subst eq
    simp at h₂
    have : i = nfa.nodes.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, NFA.Node.charStep, NFA.Node.εStep] at step
    try exact .inl step
    try exact .inl (And.right step)
  | group _ r ih =>
    apply pushRegex.group eq
    intro nfa' nfa'' nfa''' property eq₁ eq₂ eq₃ eq

    have get₂ (h : i < nfa''.val.nodes.size) : result.val[i] = nfa''.val[i] := by
      simp [eq, eq₃]
      rw [pushNode_get_lt _ h]

    have get₁ (h : i < nfa'.val.nodes.size) : result.val[i] = nfa'.val[i] := by
      rw [get₂ (Nat.lt_trans h nfa''.property)]
      rw [pushRegex_get_lt eq₂.symm _ h]

    cases Nat.eq_or_lt_of_le h₁ with
    | inl eq =>
      have : i < nfa'.val.nodes.size := eq ▸ nfa'.property
      rw [get₁ this] at step
      simp [eq₁, ←eq, Node.charStep, Node.εStep] at step
      exact .inl step
    | inr gt =>
      cases Nat.lt_or_ge i nfa''.val.nodes.size with
      | inl lt =>
        have : nfa'.val.nodes.size ≤ i := by
          simp [eq₁]
          exact gt
        have ih := ih eq₂.symm this lt (get₂ lt ▸ step)
        apply Or.inr
        cases ih with
        | inl eq =>
          rw [eq, eq₁]
          simp
        | inr ge => exact Nat.le_trans (Nat.le_of_lt nfa'.property) ge
      | inr ge =>
        simp [eq, eq₃] at h₂
        have : i = nfa''.val.nodes.size := Nat.eq_of_le_of_lt_succ ge h₂
        simp [this, eq, eq₃, Node.charStep, Node.εStep] at step
        exact .inr (Nat.le_trans (Nat.le_of_lt nfa'.property) (step ▸ ge_pushRegex_start eq₂.symm))
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ eq₂ eq₃ eq₄ eq₅ eq

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
        have : i = nfa₂.val.nodes.size := Nat.eq_of_le_of_lt_succ ge h₂
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
    intro placeholder compiled patched nfa' property
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
      simp [this, eq, eq₄, get_eq_nodes_get, eq₃, NFA.Node.charStep, NFA.Node.εStep] at step
      cases step with
      | inl eq =>
        have := ge_pushRegex_start eq₂.symm
        simp [eq₁] at this
        exact .inr (Nat.le_trans (Nat.le_succ _) (eq ▸ this))
      | inr eq => exact .inl eq

theorem done_iff_zero_pushRegex (eq : pushRegex nfa next r = result)
  (h₁ : 0 < nfa.nodes.size)
  (h₂ : ∀ (i : Nat) (isLt : i < nfa.nodes.size), nfa[i] = .done ↔ i = 0) :
  ∀ (i : Nat) (isLt : i < result.val.nodes.size), result.val[i] = .done ↔ i = 0 := by
  induction r generalizing nfa next with
  | empty | epsilon | char c | classes c =>
    try apply pushRegex.empty eq
    try apply pushRegex.epsilon eq
    try apply pushRegex.char eq
    try apply pushRegex.sparse eq
    intro eq
    subst eq
    simp
    intro i isLt
    cases Nat.eq_or_lt_of_le isLt with
    | inl eq =>
      simp at eq
      simp [eq, -List.length_eq_zero]
      exact Nat.ne_zero_iff_zero_lt.mpr h₁
    | inr lt =>
      have lt : i < nfa.nodes.size := Nat.lt_of_succ_lt_succ lt
      simp [pushNode_get_lt _ lt]
      exact h₂ i lt
  | group _ r ih =>
    apply pushRegex.group eq
    intro nfa' nfa'' nfa''' property eq₁ eq₂ eq₃ eq
    subst eq
    simp
    intro i isLt

    simp [eq₃] at isLt
    cases Nat.eq_or_lt_of_le isLt with
    | inl eq =>
      simp at eq
      simp [eq₃, eq, -List.length_eq_zero]
      exact Nat.ne_of_gt (Nat.zero_lt_of_lt nfa''.property)
    | inr lt =>
      have lt := Nat.lt_of_succ_lt_succ lt
      simp [eq₃, pushNode_get_lt _ lt]
      apply ih eq₂.symm (Nat.zero_lt_of_lt nfa'.property) ?_ i lt
      intro i isLt
      simp [eq₁] at isLt
      cases Nat.eq_or_lt_of_le isLt with
      | inl eq =>
        simp at eq
        simp [eq₁, eq, -List.length_eq_zero]
        exact Nat.ne_zero_iff_zero_lt.mpr h₁
      | inr lt =>
        have lt := Nat.lt_of_succ_lt_succ lt
        simp [eq₁, pushNode_get_lt _ lt]
        exact h₂ i lt
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq
    subst eq
    simp
    intro i isLt

    simp [eq₅] at isLt
    cases Nat.eq_or_lt_of_le isLt with
    | inl eq =>
      simp at eq
      simp [eq₅, eq, -List.length_eq_zero]
      exact Nat.ne_of_gt (Nat.zero_lt_of_lt nfa₂.property)
    | inr lt =>
      have lt := Nat.lt_of_succ_lt_succ lt
      simp [eq₅, pushNode_get_lt _ lt]
      apply ih₂ eq₃.symm (Nat.zero_lt_of_lt nfa₁.property) ?_ i lt
      intro i isLt
      apply ih₁ eq₁.symm (Nat.zero_lt_of_lt h₁) h₂ i isLt
  | concat r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    subst eq
    simp
    apply ih₁ eq₁.symm (Nat.zero_lt_of_lt nfa₂.property)
    apply ih₂ eq₂.symm h₁ h₂
  | star r ih =>
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' property
      eq₁ eq₂ eq₃ eq₄ eq
    subst eq
    simp
    intro i isLt

    match Nat.lt_trichotomy i nfa.nodes.size with
    | .inl lt =>
      have : nfa'[i] = nfa[i] := by
        have : i < placeholder.val.nodes.size :=
          Nat.lt_trans lt placeholder.property
        have : i < compiled.val.nodes.size :=
          Nat.lt_trans this compiled.property

        calc nfa'[i]
          _ = compiled.val[i] := by
            simp [eq₄, NFA.get_eq_nodes_get, eq₃]
            rw [Array.get_set_ne]
            simp
            exact Nat.ne_of_gt lt
          _ = placeholder.val[i] := by apply pushRegex_get_lt eq₂.symm
          _ = nfa[i] := by
            simp [eq₁]
            apply pushNode_get_lt
      rw [this]
      exact h₂ i lt
    | .inr (.inl eq) =>
      have : nfa'[i] = .split compiled.val.start next := by
        simp [eq₄, NFA.get_eq_nodes_get, eq₃]
        rw [Array.get_set]
        . simp [eq]
        . calc
            i = nfa.nodes.size := eq
            _ < placeholder.val.nodes.size := placeholder.property
            _ < compiled.val.nodes.size := compiled.property
      simp [this]
      exact Nat.ne_of_gt (eq ▸ h₁)
    | .inr (.inr gt) =>
      have : i < compiled.val.nodes.size := by
        simp [eq₄, eq₃] at isLt
        exact isLt
      have : nfa'[i] = compiled.val[i] := by
        simp [eq₄, NFA.get_eq_nodes_get, eq₃]
        rw [Array.get_set_ne]
        simp
        exact Nat.ne_of_lt gt
      rw [this]
      apply ih eq₂.symm (Nat.zero_lt_of_lt placeholder.property) ?_ i (by assumption)
      intro i isLt
      simp [eq₁] at isLt
      cases Nat.eq_or_lt_of_le isLt with
      | inl eq =>
        simp at eq
        simp [eq₁, eq, -List.length_eq_zero]
        exact Nat.ne_zero_iff_zero_lt.mpr h₁
      | inr lt =>
        have lt := Nat.lt_of_succ_lt_succ lt
        simp [eq₁, pushNode_get_lt _ lt]
        exact h₂ i lt

theorem done_iff_zero_compile (eq : compile r = nfa) (i : Fin nfa.nodes.size) :
  nfa[i] = .done ↔ i.val = 0 := by
  simp [←eq, compile]
  apply done_iff_zero_pushRegex rfl (by simp [done])
  intro i isLt
  simp [done] at isLt
  simp [isLt]
  rfl

theorem lt_zero_size_compile (eq : compile r = nfa) :
  0 < nfa.nodes.size := by
  simp [←eq, compile]
  set result := NFA.done.pushRegex 0 r
  exact Nat.zero_lt_of_lt result.property

end Regex.NFA
