module

import all Regex.NFA
import all Regex.NFA.Compile.Basic
public import Regex.NFA.Compile
public import RegexCorrectness.NFA.Basic
public import RegexCorrectness.Data.Expr.Semantics.Separation

import Mathlib.Tactic.Common

open Regex.Data (Expr)

public section

namespace Regex.NFA

@[grind =>]
theorem ge_pushRegex_start {nfa next e result} (eq : pushRegex nfa next e = result) :
  nfa.size ≤ result.start := by
  show nfa.size ≤ result.size - 1
  grind

open Compile.ProofData in
theorem eq_or_ge_of_step_pushRegex {nfa next e result} {i j : Nat} (eq : pushRegex nfa next e = result)
  (h₁ : nfa.size ≤ i) (h₂ : i < result.size)
  (step : (∃ c, j ∈ result[i].charStep c) ∨ j ∈ result[i].εStep) :
  j = next ∨ nfa.size ≤ j := by
  induction e generalizing nfa next result with
  | empty =>
    let pd := Empty.intro eq
    simp [pd.eq_result eq, pd.size_eq] at step h₂
    have : i = pd.nfa.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, Node.charStep, Node.εStep, pd.get_eq] at step
  | epsilon | anchor a | char c | classes cs =>
    try let pd := Epsilon.intro eq
    try let pd := Anchor.intro eq
    try let pd := Char.intro eq
    try let pd := Classes.intro eq
    simp [pd.eq_result eq, pd.size_eq] at step h₂
    have : i = pd.nfa.size := Nat.eq_of_le_of_lt_succ h₁ h₂
    simp [this, Node.charStep, Node.εStep, pd.get_eq] at step
    try exact .inl step
    try exact .inl (And.right step)
  | group _ e ih =>
    let pd := Group.intro eq
    simp [pd.eq_result eq] at step h₂

    have nlt : ¬i < pd.nfa.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    simp [nlt] at get
    split_ifs at get
    next =>
      simp [get, Node.charStep, Node.εStep] at step
      exact .inl step
    next h₁ h₂ =>
      have : j = Group.nfaClose.start ∨ Group.nfaClose.size ≤ j := by
        have : ¬i = nfa.size := h₁
        have : nfa.size < i := by omega
        have h₁ : Group.nfaClose.size ≤ i := by
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

    have nlt : ¬i < pd.nfa.size := Nat.not_lt_of_ge h₁
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

    have nlt : ¬i < pd.nfa.size := Nat.not_lt_of_ge h₁
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

    have nlt : ¬i < pd.nfa.size := Nat.not_lt_of_ge h₁
    have get := pd.get i h₂
    simp [nlt] at get
    split_ifs at get
    next => grind [Node.charStep, Node.εStep]
    next h₁' =>
      have := ih rfl (by grind) h₁' (get ▸ step)
      grind only [= Star.intro, = Star.nfaPlaceholder, = pushNode_size]
    next => grind [Node.charStep, Node.εStep]

theorem mem_save_of_mem_tags_pushRegex {nfa : NFA} {next e tag} (h : tag ∈ e.tags) :
  ∃ (i : Fin (nfa.pushRegex next e).size) (offset : Nat), (nfa.pushRegex next e)[i] = .save (2 * tag + 1) offset := by
  fun_induction pushRegex nfa next e
  next => grind [Expr.tags]
  next => grind [Expr.tags]
  next => grind [Expr.tags]
  next => grind [Expr.tags]
  next => grind [Expr.tags]
  next nfa next tag' e nfaClose nfaExpr ih =>
    simp only [Expr.tags, Finset.mem_union, Finset.mem_singleton] at h
    cases h with
    | inl eq => exact ⟨⟨nfa.size, by grind⟩, next, by grind⟩
    | inr h =>
      obtain ⟨i, offset, eq⟩ := ih h
      exact ⟨⟨i, by grind⟩, offset, by grind⟩
  next nfa next e₁ e₂ nfa₁ start₁ nfa₂ start₂ split ih₁ ih₂ =>
    simp only [Expr.tags, Finset.mem_union] at h
    cases h with
    | inl h =>
      obtain ⟨i, offset, eq⟩ := ih₁ h
      exact ⟨⟨i, by grind⟩, offset, by grind⟩
    | inr h =>
      obtain ⟨i, offset, eq⟩ := ih₂ h
      exact ⟨⟨i, by grind⟩, offset, by grind⟩
  next nfa next e₁ e₂ nfa₂ ih₂ ih₁ =>
    simp only [Expr.tags, Finset.mem_union] at h
    cases h with
    | inl h =>
      obtain ⟨i, offset, eq⟩ := ih₁ h
      exact ⟨⟨i, by grind⟩, offset, by grind⟩
    | inr h =>
      obtain ⟨i, offset, eq⟩ := ih₂ h
      exact ⟨⟨i, by grind⟩, offset, by grind⟩
  next nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    simp only [Expr.tags] at h
    obtain ⟨i, offset, eq⟩ := ih h

    let pd := Compile.ProofData.Star.intro' nfa next greedy e
    show ∃ (i : Fin pd.nfa'.size) (offset : Nat), pd.nfa'[i] = .save (2 * tag + 1) offset
    refine ⟨⟨i, by grind⟩, offset, by grind⟩

theorem mem_save_of_mem_tags_compile {e tag} (h : tag ∈ e.tags) :
∃ (i : Fin (compile e).size) (offset : Nat), (compile e)[i] = .save (2 * tag + 1) offset :=
mem_save_of_mem_tags_pushRegex h

theorem lt_of_mem_tags_compile {e tag} (h : tag ∈ e.tags) :
  2 * tag < (compile e).maxTag := by
  have ⟨i, offset, eq⟩ := mem_save_of_mem_tags_compile h
  exact (compile e).le_maxTag i eq

theorem ne_done_of_pushRegex_ge {nfa next e} (i : Nat)
  (h₁ : nfa.size ≤ i) (h₂ : i < (pushRegex nfa next e).size) :
  (pushRegex nfa next e)[i] ≠ .done := by
  fun_induction pushRegex nfa next e
  case case9 nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    let pd := Compile.ProofData.Star.intro' nfa next greedy e
    show pd.nfa'[i] ≠ .done
    let get := pd.get i h₂
    split_ifs at get
    next => grind only [= Compile.ProofData.Star.intro']
    next => grind only [= Compile.ProofData.Star.split]
    next => exact get ▸ ih (by grind) (by grind)
    next => grind only [= Compile.ProofData.Star.split]
  all_goals grind

theorem done_iff_zero_compile {e} (i : Nat) (h : i < (compile e).size) :
  (compile e)[i] = .done ↔ i = 0 := by
  apply Iff.intro
  . intro eq
    if h' : i = 0 then
      exact h'
    else
      exact (ne_done_of_pushRegex_ge i (by grind [NFA.done]) h eq).elim
  . intro eq
    show (pushRegex NFA.done 0 e)[i] = .done
    rw [pushRegex_get_lt i (by grind [NFA.done])]
    grind [NFA.done]

theorem lt_zero_size_compile {e} : 0 < (compile e).size := by
  grind [compile]

theorem lt_zero_start_compile {e} : 0 < (compile e).start := by
  show 0 < (pushRegex NFA.done 0 e).start
  grind [NFA.done]

end Regex.NFA

end
