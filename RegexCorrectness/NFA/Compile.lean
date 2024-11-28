import Regex.NFA
import Regex.NFA.Compile
import RegexCorrectness.NFA.Basic

import Mathlib.Tactic.Common

namespace Regex.NFA

-- Probably we want to state results directly about `pushRegex.val`. ProofData work better with that kind of equalities, it seems.
open Compile.ProofData in
theorem pushRegex_get_lt {nfa next e result} (eq : pushRegex nfa next e = result) (i : Nat) (h : i < nfa.nodes.size) :
  result.val[i]'(Nat.lt_trans h result.property) = nfa[i] := by
  induction e generalizing nfa next with
  | empty | epsilon | char | classes =>
    try let pd := Empty.intro eq
    try let pd := Epsilon.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.get_lt h]
    rfl
  | group _ r ih =>
    let pd := Group.intro eq

    have ih := ih (result := ⟨pd.nfaExpr, _⟩) rfl (Nat.lt_trans h pd.nfaClose_property)

    simp [pd.eq_result eq, pd.eq_push, pushNode_get_lt _ (Nat.lt_trans h pd.size_lt_nfa_expr)]
    simp [ih, Group.nfaClose]
    rw [pushNode_get_lt i]
    rfl
  | alternate r₁ r₂ ih₁ ih₂ =>
    let pd := Alternate.intro eq

    have h₁ : i < Alternate.nfa₁.nodes.size := Nat.lt_trans h pd.nfa₁_property
    have h₂ : i < Alternate.nfa₂.nodes.size := Nat.lt_trans h₁ pd.nfa₂_property

    simp [pd.eq_result eq, pd.eq_push, pushNode_get_lt i h₂]
    rw [ih₂ (result := ⟨pd.nfa₂, _⟩) rfl h₁]
    rw [ih₁ (result := ⟨pd.nfa₁, _⟩) rfl h]
    rfl
  | concat r₁ r₂ ih₁ ih₂ =>
    let pd := Concat.intro eq

    have h₂ : i < Concat.nfa₂.nodes.size := Nat.lt_trans h pd.nfa₂_property
    have ih₁ := ih₁ (result := ⟨nfa', pd.size₂_lt⟩) (Subtype.eq Concat.eq_push.symm) h₂
    have ih₂ := ih₂ (result := ⟨pd.nfa₂, pd.nfa₂_property⟩) rfl h

    simp [pd.eq_result eq, ih₁, ih₂]
    rfl
  | star r ih =>
    let pd := Star.intro eq

    have ih := ih (result := ⟨pd.nfaExpr, _⟩) rfl (Nat.lt_trans h pd.nfaPlaceholder_property)
    simp [pd.eq_result eq, pd.get_ne_start i (Nat.lt_trans h size_lt) (Nat.ne_of_lt h), ih]
    simp [Star.nfaPlaceholder]
    rw [pushNode_get_lt]
    rfl

-- Bring get_lt to `ProofData`.
namespace Compile.ProofData

namespace Group

variable [Group]

theorem get_close_expr : nfaExpr[nfa.nodes.size]'size_lt_nfa_expr = .save (2 * tag + 1) next := by
  simp [nfaExpr]
  rw [pushRegex_get_lt rfl nfa.nodes.size nfaClose_property, get_close_pre]

theorem get_close : nfa'[nfa.nodes.size]'size_lt = .save (2 * tag + 1) next := by
  simp [get_lt_expr size_lt_nfa_expr, get_close_expr]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else if _ : i = nfa.nodes.size then nfa'[i] = .save (2 * tag + 1) next
  else if _ : i < nfaExpr.nodes.size then nfa'[i] = nfaExpr[i]
  else nfa'[i] = .save (2 * tag) nfaExpr.start := by
  split_ifs
  next h' => exact pushRegex_get_lt (Subtype.eq eq'.symm) i h'
  next h' => simp [h', get_close]
  next h' => exact get_lt_expr h'
  next _ _ h' =>
    simp [eq_push] at h
    have : i ≥ nfaExpr.nodes.size := Nat.ge_of_not_lt h'
    have : i = nfaExpr.nodes.size := by
      omega
    simp [this, get_open]

theorem get_lt_close {i : Nat} (h : i < nfaClose.nodes.size) :
  nfa'[i]'(Nat.lt_trans h size_lt_close') = nfaClose[i] := by
  simp [get_lt_expr (Nat.lt_trans h nfaExpr_property)]
  simp [nfaExpr, pushRegex_get_lt rfl i h]

end Group

namespace Alternate

variable [Alternate]

theorem get_lt₂ {i : Nat} (h : i < nfa₂.nodes.size) : nfa'[i]'(Nat.lt_trans h size_lt₂) = nfa₂[i] := by
  simp [eq_push, pushNode_get_lt i h]

theorem get_lt₁ {i : Nat} (h : i < nfa₁.nodes.size) : nfa'[i]'(Nat.lt_trans h size_lt₁) = nfa₁[i] := by
  simp [get_lt₂ (Nat.lt_trans h nfa₂_property), nfa₂]
  rw [pushRegex_get_lt rfl i h]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else if _ : i < nfa₁.nodes.size then nfa'[i] = nfa₁[i]
  else if _ : i < nfa₂.nodes.size then nfa'[i] = nfa₂[i]
  else nfa'[i] = .split nfa₁.start nfa₂.start := by
  split_ifs
  next h' => exact pushRegex_get_lt (Subtype.eq eq'.symm) i h'
  next h' => exact get_lt₁ h'
  next h' => exact get_lt₂ h'
  next _ _ h' =>
    simp [eq_push] at h
    have : i ≥ nfa₂.nodes.size := Nat.ge_of_not_lt h'
    have : i = nfa₂.nodes.size := by
      omega
    simp [this, get_split]

end Alternate

namespace Concat

variable [Concat]

theorem get_lt₂ {i : Nat} (h : i < nfa₂.nodes.size) : nfa'[i]'(Nat.lt_trans h size₂_lt) = nfa₂[i] := by
  simp [eq_push, pushRegex_get_lt rfl i h]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else if _ : i < nfa₂.nodes.size then nfa'[i] = nfa₂[i]
  else True := by
  split_ifs
  next h' => exact pushRegex_get_lt (Subtype.eq eq'.symm) i h'
  next h' => exact get_lt₂ h'

end Concat

namespace Star

variable [Star]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else if _ : i = nfa.nodes.size then nfa'[i] = .split nfaExpr.start next
  else nfa'[i] = nfaExpr[i]'(size_eq_expr' ▸ h) := by
  split_ifs
  next h' => exact pushRegex_get_lt (Subtype.eq eq'.symm) i h'
  next h' => exact h' ▸ get_start
  next h' => exact get_ne_start i h h'

end Star

end Compile.ProofData

open Compile.ProofData in
theorem ge_pushRegex_start {nfa next e result} (eq : pushRegex nfa next e = result) :
  nfa.nodes.size ≤ result.val.start := by
  induction e generalizing nfa next with
  | empty | epsilon | char c | classes cs =>
    try let pd := Empty.intro eq
    try let pd := Epsilon.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.start_eq]
    rfl
  | group =>
    let pd := Group.intro eq
    simp [pd.eq_result eq, pd.start_eq]
    exact Nat.le_of_lt (Nat.lt_trans pd.nfaClose_property pd.nfaExpr_property)
  | alternate r₁ r₂ =>
    let pd := Alternate.intro eq
    simp [pd.eq_result eq, pd.eq_push]
    exact Nat.le_of_lt (Nat.lt_trans pd.nfa₁_property pd.nfa₂_property)
  | concat r₁ r₂ ih₁ =>
    let pd := Concat.intro eq
    open Concat in
    have : nfa.nodes.size ≤ nfa'.start := by
      have := ih₁ (Subtype.eq eq_push.symm)
      exact Nat.le_trans (Nat.le_of_lt nfa₂_property) this
    simp [pd.eq_result eq, this]
  | star r =>
    let pd := Star.intro eq
    simp [pd.eq_result eq, pd.start_eq]
    rfl

open Compile.ProofData in
theorem eq_or_ge_of_step_pushRegex {nfa next e result} {i j : Nat} (eq : pushRegex nfa next e = result)
  (h₁ : nfa.nodes.size ≤ i) (h₂ : i < result.val.nodes.size)
  (step : (∃ c, j ∈ result.val[i].charStep c) ∨ j ∈ result.val[i].εStep) :
  j = next ∨ nfa.nodes.size ≤ j := by
  induction e generalizing nfa next with
  | empty =>
    let pd := Empty.intro eq
    simp [pd.eq_result eq, pd.size_eq] at step h₂
    have : i = pd.nfa.nodes.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, Node.charStep, Node.εStep, pd.get_eq] at step
  | epsilon | char c | classes r =>
    try let pd := Epsilon.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.size_eq] at step h₂
    have : i = pd.nfa.nodes.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, Node.charStep, Node.εStep, pd.get_eq] at step
    try exact .inl step
    try exact .inl (And.right step)
  | group _ r ih =>
    let pd := Group.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [get, Node.charStep, Node.εStep] at step
      exact .inl step
    next h₁ h₂ =>
      have : j = Group.nfaClose.start ∨ Group.nfaClose.nodes.size ≤ j := by
        have : ¬i = nfa.nodes.size := h₁
        have : nfa.nodes.size < i := by omega
        have h₁ : Group.nfaClose.nodes.size ≤ i := by
          simp [Group.nfaClose]
          exact this
        exact ih (Subtype.eq rfl) h₁ h₂ (get ▸ step)
      simp [Group.nfaClose] at this
      cases this with
      | inl eq => exact .inr (Nat.le_of_eq eq.symm)
      | inr le => exact .inr (Nat.le_of_lt le)
    next =>
      simp [get, Node.charStep, Node.εStep] at step
      simp [step]
      exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaClose_property) (ge_pushRegex_start rfl))
  | alternate r₁ r₂ ih₁ ih₂ =>
    let pd := Alternate.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    simp [nlt] at get
    split_ifs at get
    next h₂ => exact ih₁ rfl h₁ h₂ (get ▸ step)
    next h₁ h₂ =>
      have := ih₂ rfl (Nat.le_of_not_lt h₁) h₂ (get ▸ step)
      cases this with
      | inl eq => exact .inl eq
      | inr le => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₁_property) le)
    next =>
      simp [get, Node.charStep, Node.εStep] at step
      cases step with
      | inl eq₁ => exact .inr (eq₁ ▸ (ge_pushRegex_start (result := ⟨Alternate.nfa₁, _⟩) rfl))
      | inr eq₂ =>
        have := ge_pushRegex_start (result := ⟨Alternate.nfa₂, _⟩) rfl
        exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₁_property) (eq₂ ▸ this))
  | concat r₁ r₂ ih₁ ih₂ =>
    let pd := Concat.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    split_ifs at get
    next h₂ => exact ih₂ rfl h₁ h₂ (get ▸ step)
    next h₁ =>
      have := ih₁ (result := ⟨pd.nfa', pd.size₂_lt⟩) (Subtype.eq Concat.eq_push.symm) (Nat.le_of_not_lt h₁) h₂ step
      cases this with
      | inl eq => exact .inr (eq ▸ ge_pushRegex_start rfl)
      | inr le => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₂_property) le)
  | star r ih =>
    let pd := Star.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [get, Node.charStep, Node.εStep] at step
      cases step with
      | inl eq => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaPlaceholder_property) (eq ▸ ge_pushRegex_start rfl))
      | inr eq => exact .inl eq
    next h₁' =>
      have h₁ : Star.nfaPlaceholder.nodes.size ≤ i := by
        simp [Star.nfaPlaceholder]
        omega
      have := ih rfl h₁ (pd.size_eq_expr' ▸ h₂) (get ▸ step)
      simp [Star.nfaPlaceholder] at this
      cases this with
      | inl eq => exact .inr (eq ▸ Nat.le_refl _)
      | inr le => exact .inr (Nat.le_of_lt le)

open Compile.ProofData in
theorem done_iff_zero_pushRegex {nfa next e result} (eq : pushRegex nfa next e = result)
  (h₁ : 0 < nfa.nodes.size)
  (h₂ : ∀ (i : Nat) (isLt : i < nfa.nodes.size), nfa[i] = .done ↔ i = 0) :
  ∀ (i : Nat) (isLt : i < result.val.nodes.size), result.val[i] = .done ↔ i = 0 := by
  induction e generalizing nfa next with
  | empty | epsilon | char c | classes c =>
    try let pd := Empty.intro eq
    try let pd := Epsilon.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.eq', pushRegex]
    intro i isLt
    cases Nat.eq_or_lt_of_le isLt with
    | inl eq =>
      simp at eq
      simp only [eq, pushNode_get_eq, reduceCtorEq, false_iff]
      exact Nat.ne_zero_iff_zero_lt.mpr h₁
    | inr lt =>
      simp at lt
      simp [pushNode_get_lt _ lt]
      exact h₂ i lt
  | group _ r ih =>
    let pd := Group.intro eq
    simp [pd.eq_result eq]
    intro i isLt
    have get := pd.get i isLt
    split_ifs at get <;> simp [get]
    next h => exact h₂ i h
    next h => exact Nat.ne_of_gt (h ▸ h₁)
    next h =>
      have ih := ih (result := ⟨Group.nfaExpr, _⟩) rfl (Nat.lt_trans h₁ pd.nfaClose_property)
      apply ih
      intro i isLt
      simp [Group.nfaClose] at isLt
      cases Nat.eq_or_lt_of_le isLt with
      | inl eq =>
        simp at eq
        simp only [Group.nfaClose, eq, pushNode_get_eq, reduceCtorEq, false_iff]
        exact Nat.ne_of_gt h₁
      | inr lt =>
        simp at lt
        simp [Group.nfaClose, pushNode_get_lt _ lt]
        exact h₂ i lt
    next h =>
      apply Nat.ne_of_gt
      calc
        0 < nfa.nodes.size := h₁
        _ < Group.nfaExpr.nodes.size := pd.size_lt_nfa_expr
        _ ≤ i := Nat.le_of_not_lt h
  | alternate r₁ r₂ ih₁ ih₂ =>
    let pd := Alternate.intro eq
    simp [pd.eq_result eq, pd.eq_push]

    intro i isLt
    cases Nat.eq_or_lt_of_le isLt with
    | inl eq =>
      simp at eq
      simp only [eq, pushNode_get_eq, reduceCtorEq, false_iff]
      exact Nat.ne_of_gt (Nat.zero_lt_of_lt pd.nfa₂_property)
    | inr lt =>
      simp at lt
      simp [pushNode_get_lt _ lt]
      apply ih₂ rfl (Nat.lt_trans h₁ pd.nfa₁_property)
      intro i isLt
      apply ih₁ rfl h₁ h₂
  | concat r₁ r₂ ih₁ ih₂ =>
    let pd := Concat.intro eq
    simp [pd.eq_result eq]
    apply ih₁ rfl (Nat.zero_lt_of_lt pd.nfa₂_property)
    apply ih₂ rfl h₁ h₂
  | star r ih =>
    let pd := Star.intro eq
    simp [pd.eq_result eq]
    intro i isLt
    have get := pd.get i isLt
    split_ifs at get <;> simp [get]
    next h' => exact h₂ i h'
    next h' => exact Nat.ne_of_gt (h' ▸ h₁)
    next h' =>
      apply ih rfl (Nat.zero_lt_of_lt Star.nfaPlaceholder_property)
      simp [Star.nfaPlaceholder]
      intro i isLt
      cases Nat.eq_or_lt_of_le isLt with
      | inl eq =>
        simp at eq
        simp only [eq, pushNode_get_eq, reduceCtorEq, false_iff]
        exact Nat.ne_of_gt h₁
      | inr lt =>
        simp at lt
        simp [pushNode_get_lt _ lt]
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
