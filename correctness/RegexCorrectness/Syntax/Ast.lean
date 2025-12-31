import Regex.Syntax.Ast
import RegexCorrectness.Data.Expr.Semantics.Separation
import Mathlib.Order.Interval.Finset.Basic
import Mathlib.Order.Interval.Finset.Nat

set_option autoImplicit false

open Regex.Data (Expr)

namespace Regex.Syntax.Parser


theorem charToCaseInsensitive_tags (c : Char) : (charToCaseInsensitive c).tags = ∅ := by
  simp only [charToCaseInsensitive]
  split
  case isFalse =>
    simp only [Expr.tags]
  case isTrue =>
    apply Array.foldl_induction (fun (_: ℕ) (x: Expr) => x.tags = ∅)
    · rfl
    · intro acc char h_acc
      simp [Expr.tags]
      rw [h_acc]

theorem charToCaseInsensitive_disjoint (c : Char) : Expr.Disjoint (charToCaseInsensitive c) := by
  simp only [charToCaseInsensitive]
  split
  case isFalse =>
    simp only [Expr.Disjoint]
  case isTrue =>
    apply Array.foldl_induction (fun (_: ℕ) (x: Expr) => x.Disjoint)
    · simp [Expr.Disjoint]
    · intro acc char h_acc
      simp [Expr.Disjoint]
      exact ((fun a => h_acc) ∘ fun a => c) c

end Regex.Syntax.Parser

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

theorem applyRepetitions_tags (min : Nat) (max : Option Nat) (greedy : Bool) (e : Expr) :
  (applyRepetitions min max greedy e).tags ⊆ e.tags := by
  simp only [applyRepetitions]
  grind [Expr.tags, repeatConcat_tags]

-- `Finset.ico index index'` corresponds to a half-open interval [index, index').
theorem toRegexAux_tags {index index' : ToRegexState} {ast : Ast} {e : Expr}
  (h : ast.toRegexAux index = (index', e)) :
  index.index ≤ index'.index ∧ e.tags ⊆ Finset.Ico index.index index'.index := by
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
  next state c _ =>
    simp at h
    simp [←h, charToCaseInsensitive_tags]
  next =>
    simp at h
    simp [←h, Expr.tags]
  next state ast state' e' h' ih =>
    have ⟨le, ih⟩ := ih h'
    simp only at le ih
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1 h2
    simp only [Expr.tags]
    constructor
    · omega
    · apply Finset.union_subset
      · intro x hx
        simp only [Finset.mem_singleton] at hx
        simp only [Finset.mem_Ico]
        omega
      · calc e'.tags ⊆ Finset.Ico (state.index + 1) state'.index := ih
          _ ⊆ Finset.Ico state.index state'.index := Finset.Ico_subset_Ico (by omega) (by omega)
  next state ast₁ ast₂ state₁ e₁ h₁ state₂ e₂ h₂ ih₁ ih₂ =>
    simp at h
    have ⟨le₁, ih₁⟩ := ih₁ h₁
    have ⟨le₂, ih₂⟩ := ih₂ h₂
    simp [←h, Expr.tags]
    exact ⟨Nat.le_trans le₁ le₂, Finset.Ico_union_Ico_eq_Ico le₁ le₂ ▸ Finset.union_subset_union ih₁ ih₂⟩
  next state ast₁ ast₂ state₁ e₁ h₁ state₂ e₂ h₂ ih₁ ih₂ =>
    simp at h
    have ⟨le₁, ih₁⟩ := ih₁ h₁
    have ⟨le₂, ih₂⟩ := ih₂ h₂
    simp [←h, Expr.tags]
    exact ⟨Nat.le_trans le₁ le₂, Finset.Ico_union_Ico_eq_Ico le₁ le₂ ▸ Finset.union_subset_union ih₁ ih₂⟩
  next state min max greedy ast state' e' h' ih =>
    simp at h
    have ⟨le, ih⟩ := ih h'
    simp [←h, le]
    exact Finset.Subset.trans (applyRepetitions_tags min max greedy e') ih
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

theorem repeatConcat_go_disjoint (e : Expr) (accum : Expr) (n : Nat) (h : e.Disjoint) (haccum : accum.Disjoint) :
  (repeatConcat.go e accum n).Disjoint := by
  fun_induction repeatConcat.go e accum n
  next accum => exact haccum
  next accum n ih => exact ih (by simp [Expr.Disjoint, h, haccum])

theorem repeatConcat_disjoint (e : Expr) (n : Nat) (h : e.Disjoint) : (repeatConcat e n).Disjoint :=
  repeatConcat_go_disjoint e e (n - 1) h h

theorem applyRepetitions_disjoint (min : Nat) (max : Option Nat) (greedy : Bool) (e : Expr) (h : e.Disjoint) :
  (applyRepetitions min max greedy e).Disjoint := by
  fun_cases applyRepetitions min max greedy e <;> grind [Expr.Disjoint, repeatConcat_disjoint]

theorem toRegexAux_disjoint (state : ToRegexState) (ast : Ast) : Expr.Disjoint (ast.toRegexAux state).2 := by
  fun_induction ast.toRegexAux state
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next state c _ => exact charToCaseInsensitive_disjoint c
  next => simp [Expr.Disjoint]
  next state ast state' e h ih =>
    simp [h] at ih
    simp [Expr.Disjoint, ih]
    exact Finset.not_mem_subset (toRegexAux_tags h).2 (by simp)
  next state ast₁ ast₂ state₁ e₁ h₁ state₂ e₂ h₂ ih₁ ih₂ =>
    simp [h₁, h₂] at ih₁ ih₂
    simp [Expr.Disjoint, ih₁, ih₂]
  next state ast₁ ast₂ state₁ e₁ h₁ state₂ e₂ h₂ ih₁ ih₂ =>
    simp [h₁, h₂] at ih₁ ih₂
    simp [Expr.Disjoint, ih₁, ih₂]
  next state min max greedy ast state' e h ih =>
    simp [h] at ih
    exact applyRepetitions_disjoint min max greedy e ih
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]
  next => simp [Expr.Disjoint]

theorem toRegex_disjoint (ast : Ast) : Expr.Disjoint ast.toRegex :=
  toRegexAux_disjoint ⟨ 0, false ⟩ ast

theorem toRegexAux_group_of_group {ast : Ast} : (toRegexAux ⟨ 0, false ⟩ (.group ast)).2 = .group 0 (toRegexAux ⟨ 1, false ⟩ ast).2 :=
  rfl

theorem toRegex_group_of_group (ast : Ast) : ∃ e, toRegex (.group ast) = .group 0 e :=
  ⟨(toRegexAux ⟨ 1, false ⟩ ast).2, by simp [toRegex, toRegexAux_group_of_group]⟩

end Regex.Syntax.Parser.Ast
