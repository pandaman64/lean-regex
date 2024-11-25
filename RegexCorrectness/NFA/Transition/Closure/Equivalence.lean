import RegexCorrectness.NFA.Transition.Closure.Basic
import RegexCorrectness.NFA.Transition.Path

import Mathlib.Data.List.Indexes

namespace Regex.NFA

theorem εClosure_of_pathIn {nfa : NFA} (path : nfa.pathIn lb i i' []) :
  i' ∈ nfa.εClosure i := by
  generalize h : [] = cs at path
  induction path with
  | last step =>
    subst h
    cases step with
    | εStep _ _ step => exact .step (εStep_of_εStep step) .base
  | more step _ ih =>
    simp at h
    simp [h] at *
    cases step with
    | εStep _ _ step =>
      exact εClosure.step (εStep_of_εStep step) ih

theorem eq_or_pathIn_of_εClosure {nfa : NFA} (cls : i' ∈ nfa.εClosure i) :
  i = i' ∨ nfa.pathIn 0 i i' [] := by
  induction cls with
  | base => exact .inl rfl
  | @step i j k step rest ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [εStep, lt] at step
        cases ih with
        | inl eq =>
          subst eq
          exact .inr (.last (.εStep (Nat.zero_le _) lt step))
        | inr path =>
          exact .inr (.more (.εStep (Nat.zero_le _) lt step) path)
      | isFalse nlt => simp [εStep, nlt] at step

-- TODO: explain
theorem pathIn.of_snoc_char (assm : cs' = cs ++ [c])
  (path : pathIn nfa lb i l cs') :
  ∃ j k,
    (nfa.stepIn lb i k cs' ∨ (nfa.pathIn lb i j cs ∧ nfa.stepIn lb j k [c])) ∧
    (k = l ∨ nfa.pathIn lb k l []) := by
  induction path generalizing cs with
  | @last i j cs' step =>
    cases step with
    | @charStep c' h₁ h₂ step =>
      have : [] ++ [c'] = cs ++ [c] := by simp [assm]
      have := List.append_inj' this rfl
      simp at this
      simp [this] at *
      exact ⟨0, j, .inl (.charStep h₁ h₂ step), .inl rfl⟩
    | εStep => simp at assm
  | @more i j k cs₁ cs₂ step rest ih =>
    match snoc_eq_append assm.symm with
    | .inl ⟨h₁, h₂⟩ =>
      simp [h₁, h₂] at step rest
      have := step.nil_of_snoc
      simp [this] at *
      exact ⟨0, j, .inl (assm ▸ step), .inr rest⟩
    | .inr ⟨cs₃, h₁, h₂⟩ =>
      have ⟨j', k', h₃, h₄⟩ := ih h₂
      simp [h₂] at h₃
      match h₃ with
      | .inl step' =>
        have := step'.nil_of_snoc
        simp [this, h₁, h₂] at *
        exact ⟨j, k', .inr ⟨.last step, step'⟩, h₄⟩
      | .inr ⟨path', step'⟩ =>
        simp [h₁]
        exact ⟨j', k', .inr ⟨.more step path', step'⟩, h₄⟩
where
  snoc_eq_append {cs₁ cs₂ cs₃ : List Char} {c : Char} (h : cs₁ ++ [c] = cs₂ ++ cs₃) :
    (cs₂ = cs₁ ++ [c] ∧ cs₃ = []) ∨ (∃ cs₃', cs₁ = cs₂ ++ cs₃' ∧ cs₃ = cs₃' ++ [c]) := by
    cases cs₃ using List.list_reverse_induction with
    | base =>
      simp at h
      exact .inl ⟨h.symm, rfl⟩
    | ind cs₃ c' =>
      have : c = c' ∧ cs₁ = cs₂ ++ cs₃ := by
        have h₁ := congrArg List.reverse h
        simp at h₁
        have h₂ := congrArg List.reverse h₁.right
        simp at h₂
        exact ⟨h₁.left, h₂⟩
      simp [this]

theorem eq_or_pathIn_of_reaches {nfa : NFA} {i : Fin nfa.nodes.size} {m : List Char}
  (wf : nfa.WellFormed) (h : nfa.reaches i m) :
  (nfa.start = i ∧ m = []) ∨ nfa.pathIn 0 nfa.start i m := by
  induction h with
  | nil cls =>
    cases eq_or_pathIn_of_εClosure cls with
    | inl eq => exact .inl ⟨eq, rfl⟩
    | inr path => exact .inr path
  | @snoc i j k c m _ step cls ih =>
    simp [charStep] at step
    cases ih with
    | inl eq =>
      simp [eq]
      cases eq_or_pathIn_of_εClosure cls with
      | inl eq => exact .last (.charStep (Nat.zero_le _) i.isLt (eq ▸ step))
      | inr path => exact .more (.charStep (Nat.zero_le _) i.isLt step) path
    | inr path =>
      have := path.snoc_char (by simp) wf step
      simp at this
      cases eq_or_pathIn_of_εClosure cls with
      | inl eq =>
        rw [eq] at this
        exact .inr this
      | inr path' =>
        have := this.trans path'
        simp at this
        exact .inr this

theorem reaches_of_pathIn {nfa : NFA} {i : Fin nfa.nodes.size} {m : List Char}
  (wf : nfa.WellFormed) (h : nfa.pathIn 0 nfa.start i m) :
  nfa.reaches i m := by
  induction m using List.list_reverse_induction generalizing i with
  | base => exact .nil (εClosure_of_pathIn h)
  | ind m c ih =>
    have ⟨j, k, h₁, h₂⟩ := pathIn.of_snoc_char rfl h
    have cls : i.val ∈ nfa.εClosure k := by
      cases h₂ with
      | inl eq => exact eq ▸ .base
      | inr path => exact εClosure_of_pathIn path
    match h₁ with
    | .inl step =>
      have := step.nil_of_snoc
      simp [this] at *
      cases step with
      | charStep _ _ step => exact .snoc (i := ⟨nfa.start, wf.start_lt⟩) (.nil .base) (charStep_of_charStep step) cls
    | .inr ⟨path, step⟩ =>
      have prev := ih (i := ⟨j, step.h₂⟩) path
      cases step with
      | charStep _ _ step => exact .snoc prev (charStep_of_charStep step) cls

theorem matches_of_reaches (eq : compile r = nfa)
  (h₁ : nfa.reaches i cs) (h₂ : nfa[i] = .done) :
  r.matches cs := by
  have hi : i.val = 0 := (done_iff_zero_compile eq i).mp h₂
  have path := eq_or_pathIn_of_reaches (eq ▸ compile_wf) h₁
  have : nfa.start ≠ i := by
    have : 1 ≤ nfa.start := by
      suffices done.nodes.size ≤ nfa.start by
        simp [done] at this
        exact this
      simp [←eq, compile]
      apply ge_pushRegex_start rfl
    simp [hi]
    apply Nat.ne_of_gt
    exact this
  simp [this] at path
  exact (matches_iff_pathIn eq).mpr (hi ▸ path)

theorem reaches_of_matches (eq : compile r = nfa)
  (m : r.matches cs) :
  ∃ i, nfa.reaches i cs ∧ nfa[i] = .done := by
  have := (matches_iff_pathIn eq).mp m
  let i' : Fin nfa.nodes.size := ⟨0, lt_zero_size_compile eq⟩
  have := reaches_of_pathIn (i := i') (eq ▸ compile_wf) this
  have hdone := (done_iff_zero_compile eq i').mpr rfl
  exact ⟨i', this, hdone⟩

theorem matches_iff_reaches (eq : compile r = nfa) :
  r.matches cs ↔ ∃ i, nfa.reaches i cs ∧ nfa[i] = .done :=
  ⟨reaches_of_matches eq, fun ⟨_, h₁, h₂⟩ => matches_of_reaches eq h₁ h₂⟩

end Regex.NFA
