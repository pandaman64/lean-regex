import Regex.Syntax.Ast
import RegexCorrectness.Data.Expr.Semantics.Separation
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

open Regex.Data (Expr)

namespace Regex.Syntax.Parser.Ast

theorem subset_repeatConcat_go_tags (e : Expr) (accum : Expr) (n : Nat) (h : e.tags ⊆ accum.tags) :
  e.tags ⊆ (repeatConcat.go e accum n).tags := by
  induction n generalizing accum with
  | zero => simpa [repeatConcat.go] using h
  | succ n ih =>
    dsimp [repeatConcat.go]
    exact ih (accum.concat e) (by simp [Expr.tags])

theorem repeatConcat_go_tags_subset (e : Expr) (accum : Expr) (n : Nat) :
  (repeatConcat.go e accum n).tags ⊆ accum.tags ∪ e.tags := by
  induction n generalizing accum with
  | zero => simp [repeatConcat.go]
  | succ n ih =>
    dsimp [repeatConcat.go]
    simpa [Expr.tags] using ih (accum.concat e)

theorem repeatConcat_tags (e : Expr) (n : Nat) : (repeatConcat e n).tags = e.tags := by
  refine Finset.Subset.antisymm ?_ ?_
  . simpa using repeatConcat_go_tags_subset e e (n - 1)
  . exact subset_repeatConcat_go_tags e e (n - 1) (by simp)

theorem applyRepetitions_tags (min : Nat) (max : Option Nat) (e : Expr) :
  (applyRepetitions min max e).tags ⊆ e.tags := by
  simp only [applyRepetitions]
  split
  · simp [Expr.tags]
  · simp [Expr.tags]
  · simp [Expr.tags]
  · simp [Expr.tags, repeatConcat_tags]
  · split <;> simp [Expr.tags, repeatConcat_tags]
  · split <;> simp [Expr.tags, repeatConcat_tags]

-- `Finset.ico index index'` corresponds to a half-open interval [index, index').
theorem toRegexAux_tags {index index' : Nat} {ast : Ast} {e : Expr}
  (h : ast.toRegexAux index = (index', e)) :
  index ≤ index' ∧ e.tags ⊆ Finset.Ico index index' := by
  fun_induction ast.toRegexAux index generalizing index' e
  next =>
    simp at h
    simp [←h, Expr.tags]
  next =>
    simp at h
    simp [←h, Expr.tags]
  next =>
    simp at h
    simp [←h, Expr.tags]
  next =>
    simp at h
    simp [←h, Expr.tags]
  next index ast index'' e' h' ih =>
    simp at h
    have ⟨le, ih⟩ := ih h'
    simp [←h, Expr.tags]
    refine ⟨by omega, ?_⟩
    apply Finset.union_subset
    . simp only [Finset.singleton_subset_iff, Finset.mem_Ico, le_refl, true_and]
      omega
    . exact Finset.Subset.trans ih (Finset.Ico_subset_Ico (by simp) (by simp))
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp at h
    have ⟨le₁, ih₁⟩ := ih₁ h₁
    have ⟨le₂, ih₂⟩ := ih₂ h₂
    simp [←h, Expr.tags]
    exact ⟨Nat.le_trans le₁ le₂, Finset.Ico_union_Ico_eq_Ico le₁ le₂ ▸ Finset.union_subset_union ih₁ ih₂⟩
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp at h
    have ⟨le₁, ih₁⟩ := ih₁ h₁
    have ⟨le₂, ih₂⟩ := ih₂ h₂
    simp [←h, Expr.tags]
    exact ⟨Nat.le_trans le₁ le₂, Finset.Ico_union_Ico_eq_Ico le₁ le₂ ▸ Finset.union_subset_union ih₁ ih₂⟩
  next index min max ast index'' e' h' ih =>
    simp at h
    have ⟨le, ih⟩ := ih h'
    simp [←h, le]
    exact Finset.Subset.trans (applyRepetitions_tags min max e') ih
  next =>
    simp at h
    simp [←h, Expr.tags]
  next =>
    simp at h
    simp [←h, Expr.tags]
  next =>
    simp at h
    simp [←h, Expr.tags]

theorem repeatConcat_go_disjoint (e : Expr) (accum : Expr) (n : Nat) (h : e.Disjoint) (haccum : accum.Disjoint) :
  (repeatConcat.go e accum n).Disjoint := by
  fun_induction repeatConcat.go e accum n
  next accum => exact haccum
  next accum n ih => exact ih (by simp [Expr.Disjoint, h, haccum])

theorem repeatConcat_disjoint (e : Expr) (n : Nat) (h : e.Disjoint) : (repeatConcat e n).Disjoint :=
  repeatConcat_go_disjoint e e (n - 1) h h

theorem applyRepetitions_disjoint (min : Nat) (max : Option Nat) (e : Expr) (h : e.Disjoint) :
  (applyRepetitions min max e).Disjoint := by
  fun_cases applyRepetitions min max e <;> simp_all [Expr.Disjoint, repeatConcat_disjoint]

theorem toRegexAux_disjoint (index : Nat) (ast : Ast) : Expr.Disjoint (ast.toRegexAux index).2 := by
  fun_induction ast.toRegexAux index
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next index ast index' e h ih =>
    simp [h] at ih
    simp [Expr.Disjoint, ih]
    exact Finset.not_mem_subset (toRegexAux_tags h).2 (by simp)
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp [h₁, h₂] at ih₁ ih₂
    simp [Expr.Disjoint, ih₁, ih₂]
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp [h₁, h₂] at ih₁ ih₂
    simp [Expr.Disjoint, ih₁, ih₂]
  next index min max ast index' e h ih =>
    simp [h] at ih
    exact applyRepetitions_disjoint min max e ih
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]

theorem toRegex_disjoint (ast : Ast) : Expr.Disjoint ast.toRegex :=
  toRegexAux_disjoint 0 ast

theorem toRegexAux_group_of_group {ast : Ast} : (toRegexAux 0 (.group ast)).2 = .group 0 (toRegexAux 1 ast).2 :=
  rfl

theorem toRegex_group_of_group (ast : Ast) : ∃ e, toRegex (.group ast) = .group 0 e :=
  ⟨(toRegexAux 1 ast).2, by simp [toRegex, toRegexAux_group_of_group]⟩

end Regex.Syntax.Parser.Ast
