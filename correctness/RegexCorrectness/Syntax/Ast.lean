import Regex.Syntax.Ast
import RegexCorrectness.Data.Expr.Semantics.Separation
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

open Regex.Data (Expr)

namespace Regex.Syntax.Parser.Ast

-- `Finset.ico index index`' corresponds to a half-open interval [index, index').
theorem repeatConcat_go_tags (e : Expr) (accum : Expr) (n : Nat) : 
  (repeatConcat.go e accum n).tags = accum.tags ∪ e.tags := by
  induction n generalizing accum with
  | zero => simp [repeatConcat.go]
  | succ n ih => simp [repeatConcat.go, Expr.tags, ih]

theorem repeatConcat_tags (e : Expr) (n : Nat) : (repeatConcat e n).tags = e.tags := by
  simp [repeatConcat, repeatConcat_go_tags]

theorem applyRepetitionToExpr_tags (min : Nat) (max : Option Nat) (e : Expr) :
  (applyRepetitionToExpr min max e).tags = e.tags := by
  simp only [applyRepetitionToExpr]
  split
  · simp [Expr.tags]
  · simp [Expr.tags]
  · simp [Expr.tags, repeatConcat_tags]
  · simp [Expr.tags, repeatConcat_tags]
  · split_ifs <;> simp [Expr.tags, repeatConcat_tags]
  · split_ifs <;> simp [Expr.tags, repeatConcat_tags]

theorem toRegexAux_tags {index index' : Nat} {ast : Ast} {e : Expr}
  (h : ast.toRegexAux index = (index', e)) :
  index ≤ index' ∧ e.tags = Finset.Ico index index' := by
  induction index, ast using Ast.toRegexAux.induct generalizing index' e
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]
  next index ast index'' e' h' ih =>
    simp [toRegexAux, h'] at h
    have ⟨le, ih⟩ := ih h'
    simp [←h, Expr.tags, ih]
    refine ⟨by omega, ?_⟩
    apply Finset.ext
    intro tag
    simp
    omega
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp [toRegexAux, h₁, h₂] at h
    have ⟨le₁, ih₁⟩ := ih₁ h₁
    have ⟨le₂, ih₂⟩ := ih₂ h₂
    simp [←h, Expr.tags, ih₁, ih₂]
    exact ⟨Nat.le_trans le₁ le₂, Finset.Ico_union_Ico_eq_Ico le₁ le₂⟩
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp [toRegexAux, h₁, h₂] at h
    have ⟨le₁, ih₁⟩ := ih₁ h₁
    have ⟨le₂, ih₂⟩ := ih₂ h₂
    simp [←h, Expr.tags, ih₁, ih₂]
    exact ⟨Nat.le_trans le₁ le₂, Finset.Ico_union_Ico_eq_Ico le₁ le₂⟩
  next index min max ast index'' e' h' ih =>
    simp [toRegexAux, h'] at h
    have ⟨le, ih⟩ := ih h'
    simp [←h, Expr.tags, applyRepetitionToExpr_tags, ih, le]
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]
  next =>
    simp [toRegexAux] at h
    simp [←h, Expr.tags]

theorem repeatConcat_go_disjoint (e : Expr) (accum : Expr) (n : Nat) 
  (he : Expr.Disjoint e) (haccum : Expr.Disjoint accum) 
  (hdisjoint : accum.tags ∩ e.tags = ∅) : 
  Expr.Disjoint (repeatConcat.go e accum n) := by
  induction n generalizing accum with
  | zero => simp [repeatConcat.go, haccum]
  | succ n ih => 
    simp [repeatConcat.go, Expr.Disjoint]
    apply ih
    · exact he
    · simp [Expr.Disjoint, haccum, he, hdisjoint]
    · simp [Expr.tags, hdisjoint]

theorem repeatConcat_disjoint (e : Expr) (n : Nat) (h : Expr.Disjoint e) : 
  Expr.Disjoint (repeatConcat e n) := by
  simp [repeatConcat]
  apply repeatConcat_go_disjoint
  · exact h
  · exact h  
  · simp

theorem applyRepetitionToExpr_disjoint (min : Nat) (max : Option Nat) (e : Expr) 
  (h : Expr.Disjoint e) : Expr.Disjoint (applyRepetitionToExpr min max e) := by
  simp only [applyRepetitionToExpr]
  split
  · simp [Expr.Disjoint, h]
  · simp [Expr.Disjoint, h]
  · simp [Expr.Disjoint, h, repeatConcat_disjoint]
  · simp [Expr.Disjoint, h, repeatConcat_disjoint]
  · split_ifs <;> simp [Expr.Disjoint, h, repeatConcat_disjoint]
  · split_ifs <;> simp [Expr.Disjoint, h, repeatConcat_disjoint]

theorem toRegexAux_disjoint (index : Nat) (ast : Ast) : Expr.Disjoint (ast.toRegexAux index).2 := by
  induction index, ast using Ast.toRegexAux.induct
  next => simp [toRegexAux, Expr.Disjoint]
  next => simp [toRegexAux, Expr.Disjoint]
  next => simp [toRegexAux, Expr.Disjoint]
  next => simp [toRegexAux, Expr.Disjoint]
  next index ast index' e h ih =>
    simp [h] at ih
    simp [toRegexAux, Expr.Disjoint, ih, h]
    simp [toRegexAux_tags h]
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp [h₁, h₂] at ih₁ ih₂
    simp [toRegexAux, Expr.Disjoint, h₁, h₂, ih₁, ih₂]
    simp [toRegexAux_tags h₁, toRegexAux_tags h₂]
  next index ast₁ ast₂ index₁ e₁ h₁ index₂ e₂ h₂ ih₁ ih₂ =>
    simp [h₁, h₂] at ih₁ ih₂
    simp [toRegexAux, Expr.Disjoint, h₁, h₂, ih₁, ih₂]
    simp [toRegexAux_tags h₁, toRegexAux_tags h₂]
  next index min max ast index' e h ih => 
    simp [h] at ih
    simp [toRegexAux, applyRepetitionToExpr_disjoint, ih]
  next => simp [toRegexAux, Expr.Disjoint]
  next => simp [toRegexAux, Expr.Disjoint]
  next => simp [toRegexAux, Expr.Disjoint]

theorem toRegex_disjoint (ast : Ast) : Expr.Disjoint ast.toRegex :=
  toRegexAux_disjoint 0 ast

theorem toRegexAux_group_of_group {ast : Ast} : (toRegexAux 0 (.group ast)).2 = .group 0 (toRegexAux 1 ast).2 :=
  rfl

theorem toRegex_group_of_group (ast : Ast) : ∃ e, toRegex (.group ast) = .group 0 e :=
  ⟨(toRegexAux 1 ast).2, by simp [toRegex, toRegexAux_group_of_group]⟩

end Regex.Syntax.Parser.Ast
