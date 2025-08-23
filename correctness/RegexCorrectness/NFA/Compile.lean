import Regex.NFA
import Regex.NFA.Compile
import RegexCorrectness.NFA.Basic
import RegexCorrectness.Data.Expr.Semantics.Separation

import Mathlib.Tactic.Common

set_option autoImplicit false

namespace Regex.NFA

-- Probably we want to state results directly about `pushRegex.val`. ProofData work better with that kind of equalities, it seems.
open Compile.ProofData in
theorem pushRegex_get_lt {nfa next e nfa'} (eq : pushRegex nfa next e = nfa') (i : Nat) (h : i < nfa.nodes.size) :
  nfa'[i]'(Nat.lt_trans h (eq ▸ pushRegex_size_lt)) = nfa[i] := by
  induction e generalizing nfa next nfa' with
  | empty | epsilon | anchor | char | classes =>
    try let pd := Empty.intro eq
    try let pd := Epsilon.intro eq
    try let pd := Anchor.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.get_lt h]
    rfl
  | group _ r ih =>
    let pd := Group.intro eq

    have ih := ih (nfa' := pd.nfaExpr) rfl (Nat.lt_trans h pd.nfaClose_property)

    simp [pd.eq_result eq, pd.eq_push, pushNode_get_lt _ (Nat.lt_trans h pd.size_lt_nfa_expr)]
    simp [ih, Group.nfaClose]
    rw [pushNode_get_lt i]
    rfl
  | alternate r₁ r₂ ih₁ ih₂ =>
    let pd := Alternate.intro eq

    have h₁ : i < (pd.nfa₁).nodes.size := Nat.lt_trans h pd.nfa₁_property
    have h₂ : i < (pd.nfa₂).nodes.size := Nat.lt_trans h₁ pd.nfa₂_property

    simp [pd.eq_result eq, pd.eq_push, pushNode_get_lt i h₂]
    rw [ih₂ (nfa' := pd.nfa₂) rfl h₁]
    rw [ih₁ (nfa' := pd.nfa₁) rfl h]
    rfl
  | concat r₁ r₂ ih₁ ih₂ =>
    let pd := Concat.intro eq

    have h₂ : i < (pd.nfa₂).nodes.size := Nat.lt_trans h pd.nfa₂_property
    have ih₁ := ih₁ (pd.eq_push).symm h₂
    have ih₂ := ih₂ (nfa' := pd.nfa₂) rfl h

    simp [pd.eq_result eq, ih₁, ih₂]
    rfl
  | star greedy r ih =>
    let pd := Star.intro eq

    have ih := ih (nfa' := pd.nfaExpr) rfl (Nat.lt_trans h pd.nfaPlaceholder_property)
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
  next h' => exact pushRegex_get_lt eq'.symm i h'
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
  next h' => exact pushRegex_get_lt eq'.symm i h'
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
  next h' => exact pushRegex_get_lt eq'.symm i h'
  next h' => exact get_lt₂ h'

end Concat

namespace Star

variable [Star]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else if _ : i = nfa.nodes.size then nfa'[i] = splitNode
  else nfa'[i] = nfaExpr[i]'(size_eq_expr' ▸ h) := by
  split_ifs
  next h' => exact pushRegex_get_lt eq'.symm i h'
  next h' => exact h' ▸ get_start
  next h' => exact get_ne_start i h h'

end Star

end Compile.ProofData

open Compile.ProofData in
theorem ge_pushRegex_start {nfa next e result} (eq : pushRegex nfa next e = result) :
  nfa.nodes.size ≤ result.start := by
  induction e generalizing nfa next result with
  | empty | epsilon | anchor a | char c | classes cs =>
    try let pd := Empty.intro eq
    try let pd := Epsilon.intro eq
    try let pd := Anchor.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.start_eq]
    rfl
  | group =>
    let pd := Group.intro eq
    simp [pd.eq_result eq, pd.start_eq]
    exact Nat.le_of_lt (Nat.lt_trans pd.nfaClose_property pd.nfaExpr_property)
  | alternate e₁ e₂ =>
    let pd := Alternate.intro eq
    simp [pd.eq_result eq, pd.eq_push]
    exact Nat.le_of_lt (Nat.lt_trans pd.nfa₁_property pd.nfa₂_property)
  | concat e₁ e₂ ih₁ =>
    let pd := Concat.intro eq
    open Concat in
    have : nfa.nodes.size ≤ nfa'.start := by
      have := ih₁ eq_push.symm
      exact Nat.le_trans (Nat.le_of_lt nfa₂_property) this
    simp [pd.eq_result eq, this]
  | star e =>
    let pd := Star.intro eq
    simp [pd.eq_result eq, pd.start_eq]
    rfl

open Compile.ProofData in
theorem eq_or_ge_of_step_pushRegex {nfa next e result} {i j : Nat} (eq : pushRegex nfa next e = result)
  (h₁ : nfa.nodes.size ≤ i) (h₂ : i < result.nodes.size)
  (step : (∃ c, j ∈ result[i].charStep c) ∨ j ∈ result[i].εStep) :
  j = next ∨ nfa.nodes.size ≤ j := by
  induction e generalizing nfa next result with
  | empty =>
    let pd := Empty.intro eq
    simp [pd.eq_result eq, pd.size_eq] at step h₂
    have : i = pd.nfa.nodes.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, Node.charStep, Node.εStep, pd.get_eq] at step
  | epsilon | anchor a | char c | classes cs =>
    try let pd := Epsilon.intro eq
    try let pd := Anchor.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.size_eq] at step h₂
    have : i = pd.nfa.nodes.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, Node.charStep, Node.εStep, pd.get_eq] at step
    try exact .inl step
    try exact .inl (And.right step)
  | group _ e ih =>
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
        exact ih rfl h₁ h₂ (get ▸ step)
      simp [Group.nfaClose] at this
      cases this with
      | inl eq => exact .inr (Nat.le_of_eq eq.symm)
      | inr le => exact .inr (Nat.le_of_lt le)
    next =>
      simp [get, Node.charStep, Node.εStep] at step
      simp [step]
      exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaClose_property) (ge_pushRegex_start rfl))
  | alternate e₁ e₂ ih₁ ih₂ =>
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
      | inl eq₁ => exact .inr (eq₁ ▸ (ge_pushRegex_start (result := pd.nfa₁) rfl))
      | inr eq₂ =>
        have := ge_pushRegex_start (result := pd.nfa₂) rfl
        exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₁_property) (eq₂ ▸ this))
  | concat e₁ e₂ ih₁ ih₂ =>
    let pd := Concat.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    split_ifs at get
    next h₂ => exact ih₂ rfl h₁ h₂ (get ▸ step)
    next h₁ =>
      have := ih₁ (pd.eq_push).symm (Nat.le_of_not_lt h₁) h₂ step
      cases this with
      | inl eq => exact .inr (eq ▸ ge_pushRegex_start rfl)
      | inr le => exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfa₂_property) le)
  | star greedy e ih =>
    let pd := Star.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.nodes.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [get, Node.charStep, Node.εStep, Star.splitNode] at step
      cases step with
      | inl eq =>
        split at eq
        . exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaPlaceholder_property) (eq ▸ ge_pushRegex_start rfl))
        . exact .inl eq
      | inr eq =>
        split at eq
        . exact .inl eq
        . exact .inr (Nat.le_trans (Nat.le_of_lt pd.nfaPlaceholder_property) (eq ▸ ge_pushRegex_start rfl))
    next h₁' =>
      have h₁ : Star.nfaPlaceholder.nodes.size ≤ i := by
        simp [Star.nfaPlaceholder]
        omega
      have := ih rfl h₁ (pd.size_eq_expr' ▸ h₂) (get ▸ step)
      simp [Star.nfaPlaceholder] at this
      cases this with
      | inl eq => exact .inr (eq ▸ Nat.le_refl _)
      | inr le => exact .inr (Nat.le_of_lt le)

open Compile.ProofData Data.Expr in
theorem mem_save_of_mem_tags_pushRegex {nfa next e result tag} (eq : pushRegex nfa next e = result)
  (h : tag ∈ e.tags) :
  ∃ (i j : Fin result.nodes.size) (offset offset' : Nat),
    result[i] = .save (2 * tag) offset ∧ result[j] = .save (2 * tag + 1) offset' := by
  induction e generalizing nfa next result with
  | empty | epsilon | anchor | char | classes => simp [tags] at h
  | group tag' e ih =>
    let pd := Group.intro eq
    rw [pd.eq_result eq]

    simp [tags] at h
    cases h with
    | inl eq =>
      refine ⟨⟨(pd.nfaExpr).nodes.size, pd.size_lt_expr'⟩, ⟨(pd.nfa).nodes.size, pd.size_lt⟩, (pd.nfaExpr).start, pd.next, ?_⟩
      simp [pd.get_open, pd.get_close, eq]
      rfl
    | inr h =>
      have ⟨i, j, offset, offset', eq'⟩ := ih (result := pd.nfaExpr) rfl h
      simp at eq'
      have iLt' := Nat.lt_trans i.isLt pd.size_lt_expr'
      have jLt' := Nat.lt_trans j.isLt pd.size_lt_expr'
      refine ⟨⟨i, iLt'⟩, ⟨j, jLt'⟩, offset, offset', ?_⟩
      have eqi : nfa'[i.val] = pd.nfaExpr[i] := by
        simp [pd.eq_push, pushNode_get_lt]
      have eqj : nfa'[j.val] = pd.nfaExpr[j] := by
        simp [pd.eq_push, pushNode_get_lt]
      simp [eqi, eqj, eq']
  | alternate e₁ e₂ ih₁ ih₂ =>
    let pd := Alternate.intro eq
    rw [pd.eq_result eq]

    simp [tags] at h
    cases h with
    | inl h =>
      have ⟨i, j, offset, offset', eq'⟩ := ih₁ (result := pd.nfa₁) rfl h
      simp at eq' i j
      refine ⟨⟨i, Nat.lt_trans i.isLt pd.size_lt₁⟩, ⟨j, Nat.lt_trans j.isLt pd.size_lt₁⟩, offset, offset', ?_⟩
      simp [pd.get_lt₁, eq']
    | inr h =>
      have ⟨i, j, offset, offset', eq'⟩ := ih₂ (result := pd.nfa₂) rfl h
      simp at eq' i j
      refine ⟨⟨i, Nat.lt_trans i.isLt pd.size_lt₂⟩, ⟨j, Nat.lt_trans j.isLt pd.size_lt₂⟩, offset, offset', ?_⟩
      simp [pd.get_lt₂, eq']
  | concat e₁ e₂ ih₁ ih₂ =>
    let pd := Concat.intro eq
    rw [pd.eq_result eq]

    simp [tags] at h
    cases h with
    | inl h => exact ih₁ (nfa := pd.nfa₂) rfl h
    | inr h =>
      have ⟨i, j, offset, offset', eq'⟩ := ih₂ (result := pd.nfa₂) rfl h
      simp at eq' i j
      refine ⟨⟨i, Nat.lt_trans i.isLt pd.size₂_lt⟩, ⟨j, Nat.lt_trans j.isLt pd.size₂_lt⟩, offset, offset', ?_⟩
      simp [pd.get_lt₂, eq']
  | star greedy e ih =>
    let pd := Star.intro eq
    rw [pd.eq_result eq]

    simp [tags] at h
    have ⟨i, j, offset, offset', eq'⟩ := ih (result := pd.nfaExpr) rfl h
    simp at eq' i j
    have ilt : i < nfa'.nodes.size := by simp [pd.size_eq_expr']
    have jlt : j < nfa'.nodes.size := by simp [pd.size_eq_expr']
    refine ⟨⟨i, ilt⟩, ⟨j, jlt⟩, offset, offset', ⟨?_, ?_⟩⟩
    . simp
      have := pd.get i ilt
      split_ifs at this
      next h =>
        have ilt' : i < (pd.nfaPlaceholder).nodes.size := by
          simp [Star.nfaPlaceholder]
          omega
        have : nfa'[i.val] = pd.nfaExpr[i] :=
          calc
            _ = nfa[i] := pushRegex_get_lt rfl i h
            _ = pd.nfaPlaceholder[i] := by
              simp [Star.nfaPlaceholder, pushNode_get_lt i h]
              rfl
            _ = pd.nfaExpr[i] := (pushRegex_get_lt rfl i ilt').symm
        simp [this, eq']
      next h =>
        have ilt' : i < (pd.nfaPlaceholder).nodes.size := by
          simp [Star.nfaPlaceholder, h]
        have : pd.nfaExpr[i] = .fail :=
          calc
            _ = pd.nfaPlaceholder[i] := pushRegex_get_lt rfl i ilt'
            _ = .fail := by simp [h, Star.nfaPlaceholder]
        simp [eq'] at this
      next => simp [this, eq']
    . simp
      have := pd.get j jlt
      split_ifs at this
      next h =>
        have jlt' : j < (pd.nfaPlaceholder).nodes.size := by
          simp [Star.nfaPlaceholder]
          omega
        have : nfa'[j.val] = pd.nfaExpr[j] :=
          calc
            _ = nfa[j] := pushRegex_get_lt rfl j h
            _ = pd.nfaPlaceholder[j] := by
              simp [Star.nfaPlaceholder, pushNode_get_lt j h]
              rfl
            _ = pd.nfaExpr[j] := (pushRegex_get_lt rfl j jlt').symm
        simp [this, eq']
      next h =>
        have jlt' : j < (pd.nfaPlaceholder).nodes.size := by
          simp [Star.nfaPlaceholder, h]
        have : pd.nfaExpr[j] = .fail :=
          calc
            _ = pd.nfaPlaceholder[j] := pushRegex_get_lt rfl j jlt'
            _ = .fail := by simp [h, Star.nfaPlaceholder]
        simp [eq'] at this
      next => simp [this, eq']

theorem mem_save_of_mem_tags_compile {e nfa tag} (eq : compile e = nfa) (h : tag ∈ e.tags) :
  ∃ (i j : Fin nfa.nodes.size) (offset offset' : Nat),
    nfa[i] = .save (2 * tag) offset ∧ nfa[j] = .save (2 * tag + 1) offset' := by
  have := mem_save_of_mem_tags_pushRegex (result := NFA.done.pushRegex 0 e) rfl h
  simp [compile] at eq
  rw [eq] at this
  exact this

theorem lt_of_mem_tags_compile {e nfa tag} (eq : compile e = nfa) (h : tag ∈ e.tags) :
  2 * tag < nfa.maxTag := by
  have ⟨_, j, _, offset', _, hn⟩ := mem_save_of_mem_tags_compile eq h
  exact nfa.le_maxTag j hn

open Compile.ProofData in
theorem done_iff_zero_pushRegex {nfa next e result} (eq : pushRegex nfa next e = result)
  (h₁ : 0 < nfa.nodes.size)
  (h₂ : ∀ (i : Nat) (isLt : i < nfa.nodes.size), nfa[i] = .done ↔ i = 0) :
  ∀ (i : Nat) (isLt : i < result.nodes.size), result[i] = .done ↔ i = 0 := by
  induction e generalizing nfa next result with
  | empty | epsilon | anchor a | char c | classes c =>
    try let pd := Empty.intro eq
    try let pd := Epsilon.intro eq
    try let pd := Anchor.intro eq
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
      have ih := ih (result := pd.nfaExpr) rfl (Nat.lt_trans h₁ pd.nfaClose_property)
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
  | star greedy r ih =>
    let pd := Star.intro eq
    simp [pd.eq_result eq]
    intro i isLt
    have get := pd.get i isLt
    split_ifs at get <;> simp [get]
    next h' => exact h₂ i h'
    next h' =>
      simp [Star.splitNode]
      exact Nat.ne_of_gt (h' ▸ h₁)
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

theorem done_iff_zero_compile {e nfa} (eq : compile e = nfa) (i : Fin nfa.nodes.size) :
  nfa[i] = .done ↔ i.val = 0 := by
  simp [←eq, compile]
  apply done_iff_zero_pushRegex rfl (by simp [done])
  intro i isLt
  simp [done] at isLt
  simp [isLt]
  rfl

theorem lt_zero_size_compile {e nfa} (eq : compile e = nfa) :
  0 < nfa.nodes.size := by
  simp [←eq, compile]
  exact Nat.zero_lt_of_lt pushRegex_size_lt

theorem lt_zero_start_compile {e nfa} (eq : compile e = nfa) :
  0 < nfa.start := by
  simp [←eq, compile]
  exact ge_pushRegex_start (nfa := done) rfl

end Regex.NFA
