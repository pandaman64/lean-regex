import Regex.Lemmas
import Regex.NFA.Basic

import Mathlib.Data.Set.Basic

open Set

namespace NFA.Transition

def charStep (nodes : Array Node) (c : Char) (i : Nat) : Set Nat :=
  if h : i < nodes.size then
    match nodes[i] with
    | .char c' next => if c = c' then {next} else ∅
    | _ => ∅
  else
    ∅

def εStep (nodes : Array Node) (i : Nat) : Set Nat :=
  if h : i < nodes.size then
    match nodes[i] with
    | .epsilon next => {next}
    | .split next₁ next₂ => {next₁, next₂}
    | _ => ∅
  else
    ∅

inductive εClosure (nodes : Array Node) : Nat → Set Nat where
  | base : εClosure nodes i i
  | step {i j k : Nat} (head : j ∈ εStep nodes i) (tail : εClosure nodes j k) : εClosure nodes i j

def εClosureSet (nodes : Array Node) (S : Set Nat) : Set Nat
  | j => ∃ i ∈ S, j ∈ εClosure nodes i

@[simp]
theorem subset_εClosureSet : S ⊆ εClosureSet nodes S := by
  intro i h
  exists i
  exact ⟨h, .base⟩

@[simp]
theorem εClosureSet_singleton_base : i ∈ εClosureSet nodes {i} := by
  exists i
  exact ⟨mem_singleton _, .base⟩

@[simp]
theorem εClosureSet_singleton_step {i j : Nat} (h : j ∈ εStep nodes i) : j ∈ εClosureSet nodes {i} := by
  exists i
  exact ⟨mem_singleton _, .step h .base⟩

@[simp]
theorem εClosureSet_empty : εClosureSet nodes ∅ = ∅ := by
  apply eq_empty_of_forall_not_mem
  intro i h
  induction h with
  | intro _ h => apply not_mem_empty _ h.left

@[simp]
theorem εClosureSet_univ : εClosureSet nodes univ = univ := by
  apply eq_univ_of_forall
  intro i
  exists i
  exact ⟨mem_univ _, .base⟩

theorem εClosureSet_monotone : Monotone (εClosureSet nodes) := by
  intro S₁ S₂ hsub
  simp [subset_def]
  intro j hm
  let ⟨i, h, cls⟩ := hm
  have hsub' : i ∈ S₂ := mem_of_subset_of_mem hsub h
  cases cls with
  | base => exact mem_of_subset_of_mem subset_εClosureSet hsub'
  | step head tail => exact ⟨i, hsub', .step head tail⟩

def stepSet (nodes : Array Node) (S : Set Nat) (c : Char) : Set Nat
  | j => ∃ i ∈ S, j ∈ εClosureSet nodes (charStep nodes c i)

@[simp]
def stepSet_empty : stepSet nodes ∅ c = ∅ := by
  apply eq_empty_of_forall_not_mem
  intro i h
  induction h with
  | intro _ h => apply not_mem_empty _ h.left

@[simp]
def mem_stepSet_iff : j ∈ stepSet nodes S c ↔ ∃ i ∈ S, j ∈ εClosureSet nodes (charStep nodes c i) := by
  apply Iff.intro
  . intro h; exact h
  . intro h; exact h

theorem stepSet_monotone (c : Char) : Monotone fun S => stepSet nodes S c := by
  intro S₁ S₂ h
  simp [subset_def]
  intro j i hi hj
  exact ⟨i, mem_of_subset_of_mem h hi, hj⟩

def evalFrom (nodes : Array Node) (S : Set Nat) : List Char → Set Nat :=
  List.foldl (stepSet nodes) (εClosureSet nodes S)

theorem evalFrom_monotone :
  Monotone fun S => evalFrom nodes S cs := by
  intro S₁ S₂ h
  simp
  apply List.foldl_monotone stepSet_monotone cs
  exact εClosureSet_monotone h

#check List.foldl_monotone
#check List.foldl_strictMono

theorem evalFrom_append (eq : s = s₁ ++ s₂) :
  evalFrom nodes S s = List.foldl (stepSet nodes) (evalFrom nodes S s₁) s₂ := by
  conv =>
    lhs
    rw [eq, evalFrom, List.foldl_append]

theorem subset_evalFrom_append (nodes : Array Node) (S : Set Nat) (eq : s = s₁ ++ s₂) :
  evalFrom nodes S s ⊆ evalFrom nodes (evalFrom nodes S s₁) s₂ := by
  rw [evalFrom_append eq]
  apply List.foldl_monotone stepSet_monotone s₂
  exact subset_εClosureSet

-- theorem evalFrom_of_matches (eq : compileRaw.loop nodes next r = result)
--   (m : r.matches s) : next ∈ evalFrom result.1 {result.2.val} s.data := by
--   induction m generalizing nodes next result with
--   | char c eqs =>
--     simp [eqs, evalFrom, List.foldl]
--     simp [compileRaw.loop] at eq
--     exists result.2
--     subst eq
--     simp [addNode, charStep]
--   | epsilon eqs =>
--     simp [eqs, evalFrom, List.foldl]
--     simp [compileRaw.loop] at eq
--     subst eq
--     exists nodes.size
--     simp [addNode]
--     exact εClosure.step (by simp [εStep]) .base
--   | @alternateLeft s r₁ r₂ m ih =>
--     let result₁ := compileRaw.loop nodes next r₁
--     let result₂ := compileRaw.loop result₁.1 next r₂
--     let result' := addNode result₂.1 (.split result₁.2 result₂.2)

--     let x := ih (nodes := nodes) (next := next) rfl

--     have : result.2.val = result'.2.val := by rw [eq.symm, compileRaw.loop]
--     rw [this]
--     have : result.1.val = result'.1.val := by rw [eq.symm, compileRaw.loop]
--     rw [this]

--     simp [addNode, evalFrom]

--     sorry
--   | alternateRight => sorry
--   | concat s s₁ s₂ r₁ r₂ eqs m₁ m₂ ih₁ ih₂ =>
--     let result₂ := compileRaw.loop nodes next r₂
--     let result₁ := compileRaw.loop result₂.1 result₂.2 r₁

--     have : result.2.val = result₁.2.val := by rw [eq.symm, compileRaw.loop]
--     rw [this]
--     have : result.1.val = result₁.1.val := by rw [eq.symm, compileRaw.loop]
--     rw [this]

--     have eqs : s.data = s₁.data ++ s₂.data := by rw [eqs, String.data_append]
--     let x := subset_evalFrom_append result₂.1.val {result₂.2.val} eqs

--     let ih₁ : result₂.2.val ∈ evalFrom result₁.1.val {result₁.2.val} s₁.data := ih₁ rfl
--     let ih₂ : next ∈ evalFrom result₂.1.val {result₂.2.val} s₂.data := ih₂ rfl

--     sorry
--   | star => sorry

end NFA.Transition

#check List.foldl_eq_foldr'
#check List.foldl_monotone
