-- When the regex matches a string, the compiled NFA accepts it.
import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Order
import RegexCorrectness.NFA.Transition.Basic
import RegexCorrectness.Lemmas

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

open Set

namespace NFA

theorem sub_εStep_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) :
  nfa₁.εStep i ⊆ nfa₂.εStep i := by
  if h : i < nfa₁.nodes.size then
    have : i < nfa₂.nodes.size := Nat.lt_of_lt_of_le h (le_size_of_le le)
    simp [εStep, h, this]
    obtain ⟨_, le⟩ := le ⟨i, h⟩
    exact le.right
  else
    simp [εStep, h]

theorem sub_charStep_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) :
  nfa₁.charStep i c ⊆ nfa₂.charStep i c := by
  if h : i < nfa₁.nodes.size then
    have : i < nfa₂.nodes.size := Nat.lt_of_lt_of_le h (le_size_of_le le)
    simp [charStep, h, this]
    obtain ⟨_, le⟩ := le ⟨i, h⟩
    exact le.left c
  else
    simp [charStep, h]

-- FIXME: I wanted to make this a claim about `Fin nfa.nodes.size`, but it's super cumbersome
-- to cast between `Fin nfa₁.nodes.size` and `Fin nfa₂.nodes.size` given `nfa₁ ≤ nfa₂`.
-- I should have avoided using NFA's ordering for proofs...
inductive εClosure (nfa : NFA) : Nat → Set Nat where
  | base : nfa.εClosure i i
  | step {i j k : Nat} (step : j ∈ nfa.εStep i) (rest : nfa.εClosure j k) :
    nfa.εClosure i k

-- theorem lt_of_εClosure_left {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i) :
--   i < nfa.nodes.size := by
--   cases h with
--   | base h => exact h
--   | step h => exact h

theorem lt_of_εClosure_right {nfa : NFA} {i j : Nat}
  (lt : i < nfa.nodes.size) (h : j ∈ nfa.εClosure i) :
  j < nfa.nodes.size := by
  induction h with
  | base => exact lt
  | @step i j _ step _ ih =>
    have : j < nfa.nodes.size := by
      simp [εStep] at step
      split at step <;> exact lt_of_εStep step
    exact ih this

theorem εClosure_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : j ∈ nfa₁.εClosure i) :
  j ∈ nfa₂.εClosure i := by
  induction h with
  | base => exact .base
  | step step _ ih => exact .step (mem_of_subset_of_mem (sub_εStep_of_le le) step) ih

theorem εClosure_subset_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) :
  nfa₁.εClosure i ⊆ nfa₂.εClosure i := by
  intro j h
  exact εClosure_of_le le h

theorem εClosure_snoc {nfa : NFA} (cls : j ∈ nfa.εClosure i) (step : k ∈ nfa.εStep j) :
  k ∈ nfa.εClosure i := by
  induction cls with
  | base => exact .step step .base
  | step step' _ ih => exact εClosure.step step' (ih step)

theorem εClosure_trans {nfa : NFA} (h₁ : j ∈ nfa.εClosure i) (h₂ : k ∈ nfa.εClosure j) :
  k ∈ nfa.εClosure i := by
  induction h₁ with
  | base => exact h₂
  | step head _ ih => exact .step head (ih h₂)

theorem subset_εClosure_of_mem {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i) :
  nfa.εClosure j ⊆ nfa.εClosure i := by
  intro k h'
  exact εClosure_trans h h'

-- Useful theorem when proving that reachability algorithm gives the εClosure
theorem mem_εStep_iff_εClosure_sub {nfa : NFA} {S : Set Nat} :
  (∀ i ∈ S, (_ : i < nfa.nodes.size) → ∀ j ∈ nfa[i].εStep, j ∈ S) ↔
  ∀ i ∈ S, nfa.εClosure i ⊆ S := by
  apply Iff.intro
  . intro assm i mem
    intro k cls
    induction cls with
    | base => exact mem
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [εStep, lt] at step
        exact ih (assm i mem lt j step)
      | isFalse nlt => simp [εStep, nlt] at step
  . intro assm i mem _ j step
    apply Set.mem_of_mem_of_subset _ (assm i mem)
    exact εClosure.step (εStep_of_εStep step) .base

def εClosureSet (nfa : NFA) (S : Set Nat) : Set Nat := ⋃ i ∈ S, nfa.εClosure i

@[simp]
theorem subset_εClosureSet {nfa : NFA} : S ⊆ nfa.εClosureSet S := by
  intro i mem
  simp [εClosureSet]
  refine ⟨i, mem, ?_⟩
  exact .base

@[simp]
theorem εClosureSet_singleton_base {nfa : NFA} : i ∈ nfa.εClosureSet {i} := by
  simp [εClosureSet]
  exact .base

@[simp]
theorem εClosureSet_singleton_step {nfa : NFA} {i j : Nat}
  (h : i < nfa.nodes.size) (mem : j ∈ nfa[i].εStep) : j ∈ nfa.εClosureSet {i} := by
  simp [εClosureSet]
  exact .step (by simp [h, mem, εStep]) .base

@[simp]
theorem εClosureSet_singleton {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i):
  j ∈ nfa.εClosureSet {i} := by
  apply mem_iUnion_of_mem i
  simp [h]

@[simp]
theorem εClosureSet_empty {nfa : NFA} : nfa.εClosureSet ∅ = ∅ := by
  simp [εClosureSet]

@[simp]
theorem εClosureSet_univ {nfa : NFA} : nfa.εClosureSet univ = univ :=
  univ_subset_iff.mp subset_εClosureSet

theorem εClosureSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.εClosureSet S₁ ⊆ nfa₂.εClosureSet S₂ := by
  apply biUnion_mono hs
  intro i _
  exact εClosure_subset_of_le hn

@[simp]
theorem εClosureSet_idempotent {nfa : NFA} : nfa.εClosureSet (nfa.εClosureSet S) = nfa.εClosureSet S := by
  apply eq_of_subset_of_subset
  . simp [subset_def]
    intro k h
    simp [mem_iUnion, εClosureSet] at h
    let ⟨i, h, j, cls, cls'⟩ := h
    exact mem_iUnion_of_mem i (mem_iUnion_of_mem h (εClosure_trans cls cls'))
  . apply subset_εClosureSet

theorem εClosureSet_iUnion_distrib {nfa : NFA} {S : Set α} {f : α → Set Nat} :
  nfa.εClosureSet (⋃ i ∈ S, f i) = ⋃ i ∈ S, nfa.εClosureSet (f i) := by
  simp [εClosureSet]

theorem εClosureSet_union_distrib {nfa : NFA} {S₁ S₂ : Set Nat} :
  nfa.εClosureSet (S₁ ∪ S₂) = nfa.εClosureSet S₁ ∪ nfa.εClosureSet S₂ := by
  apply eq_of_subset_of_subset
  . simp [subset_def]
    intro j h
    simp [εClosureSet] at *
    let ⟨i, h, cls⟩ := h
    cases h with
    | inl h => exact .inl ⟨i, h, cls⟩
    | inr h => exact .inr ⟨i, h, cls⟩
  . simp [subset_def]
    intro j h
    simp [εClosureSet] at *
    cases h with
    | inl h =>
      let ⟨i, h, cls⟩ := h
      exact ⟨i, .inl h, cls⟩
    | inr h =>
      let ⟨i, h, cls⟩ := h
      exact ⟨i, .inr h, cls⟩

theorem εClosureSet_of_εStep {nfa : NFA} {i j : Nat} (step : j ∈ nfa.εStep i) :
  nfa.εClosureSet {j} ⊆ nfa.εClosureSet {i} := by
  suffices nfa.εClosureSet {j} ⊆ nfa.εClosureSet (nfa.εClosureSet {i}) by
    simp [εClosureSet_idempotent] at this
    exact this
  apply εClosureSet_subset le_refl
  simp [εClosureSet]
  exact .step step .base

def stepSet (nfa : NFA) (S : Set Nat) (c : Char) : Set Nat :=
  ⋃ i ∈ S, nfa.εClosureSet (nfa.charStep i c)

@[simp]
def stepSet_empty {nfa : NFA} : nfa.stepSet ∅ c = ∅ := by
  simp [stepSet]

@[simp]
theorem εClosureSet_stepSet {nfa : NFA} :
  nfa.εClosureSet (nfa.stepSet S c) = nfa.stepSet S c := by
  apply eq_of_subset_of_subset
  . conv =>
      lhs
      simp [stepSet, εClosureSet_iUnion_distrib]
  . exact subset_εClosureSet

theorem stepSet_iUnion_distrib {nfa : NFA} {f : α → Set Nat} {S : Set α} {c : Char} :
  nfa.stepSet (⋃ i ∈ S, f i) c = ⋃ i ∈ S, nfa.stepSet (f i) c := by
  simp [stepSet]

theorem stepSet_union_distrib {nfa : NFA} {S₁ S₂ : Set Nat} :
  nfa.stepSet (S₁ ∪ S₂) c = nfa.stepSet S₁ c ∪ nfa.stepSet S₂ c := by
  simp [stepSet, εClosureSet_union_distrib]
  apply eq_of_subset_of_subset
  . intro j
    simp
    intro i mem cls
    cases mem with
    | inl mem => exact .inl ⟨i, mem, cls⟩
    | inr mem => exact .inr ⟨i, mem, cls⟩
  . intro j
    simp
    intro h
    match h with
    | .inl ⟨i, mem, cls⟩ => exact ⟨i, .inl mem, cls⟩
    | .inr ⟨i, mem, cls⟩ => exact ⟨i, .inr mem, cls⟩

theorem stepSet_insert_distrib {nfa : NFA} :
  nfa.stepSet (insert i S) c = nfa.stepSet S c ∪ nfa.stepSet {i} c := by
  have : nfa.stepSet (S ∪ {i}) c =  nfa.stepSet S c ∪ nfa.stepSet {i} c :=
    stepSet_union_distrib
  simp at this
  exact this

theorem stepSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.stepSet S₁ c ⊆ nfa₂.stepSet S₂ c := by
  simp [subset_def, stepSet]
  intro j i h₁ h₂

  exact ⟨
    i,
    mem_of_subset_of_mem hs h₁,
    mem_of_subset_of_mem (εClosureSet_subset hn (sub_charStep_of_le hn)) h₂
  ⟩

theorem lt_of_mem_stepSet {nfa : NFA} (h : j ∈ nfa.stepSet S c) :
  j < nfa.nodes.size := by
  simp [stepSet] at h
  let ⟨i, _, cls⟩ := h
  simp [εClosureSet] at cls
  obtain ⟨i', step, cls⟩ := cls
  have : i' < nfa.nodes.size := by
    simp [charStep] at step
    split at step <;> try simp at step
    exact lt_of_charStep step
  exact lt_of_εClosure_right this cls

theorem foldl_stepSet_empty {nfa : NFA} :
  List.foldl nfa.stepSet ∅ cs = ∅ := by
  induction cs with
  | nil => simp
  | cons c cs ih => simp [ih]

theorem foldl_stepSet_subset_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : S₁ ⊆ S₂) :
  List.foldl nfa₁.stepSet S₁ cs ⊆ List.foldl nfa₂.stepSet S₂ cs := by
  induction cs generalizing S₁ S₂ with
  | nil => simp [h]
  | cons c _ ih =>
    simp
    apply ih
    exact stepSet_subset le h

theorem foldl_stepSet_subset {nfa : NFA} (h : S₁ ⊆ S₂) :
  List.foldl nfa.stepSet S₁ cs ⊆ List.foldl nfa.stepSet S₂ cs :=
  foldl_stepSet_subset_of_le le_refl h

theorem foldl_stepSet_iUnion_distrib {nfa : NFA} {S : Set α} {f : α → Set Nat} :
  List.foldl nfa.stepSet (⋃ i ∈ S, f i) cs = ⋃ i ∈ S, List.foldl nfa.stepSet (f i) cs := by
  induction cs generalizing S f with
  | nil => simp
  | cons c _ ih => simp [stepSet, ih]

theorem εClosureSet_subset_foldl_stepSet {nfa : NFA} (h : S' ⊆ List.foldl nfa.stepSet (nfa.εClosureSet S) cs) :
  nfa.εClosureSet S' ⊆ List.foldl nfa.stepSet (nfa.εClosureSet S) cs := by
  induction cs generalizing S S' with
  | nil =>
    simp at *
    calc nfa.εClosureSet S'
      _ ⊆ nfa.εClosureSet (nfa.εClosureSet S) := εClosureSet_subset le_refl h
      _ = nfa.εClosureSet S := εClosureSet_idempotent
  | cons c _ ih =>
    simp at *
    simp [stepSet, ←εClosureSet_iUnion_distrib]
    apply ih
    apply Subset.trans h
    apply foldl_stepSet_subset
    simp [stepSet]
    intro i hi j hj
    simp [εClosureSet_iUnion_distrib]
    exact ⟨i, hi, hj⟩

def evalFrom (nfa : NFA) (S : Set Nat) : List Char → Set Nat :=
  List.foldl (nfa.stepSet) (nfa.εClosureSet S)

theorem mem_evalFrom_subset {nfa : NFA} (hmem : next ∈ nfa.evalFrom S₁ s) (hs : S₁ ⊆ nfa.εClosureSet S₂) :
  next ∈ nfa.evalFrom S₂ s := by
  apply mem_of_subset_of_mem _ hmem
  apply le_foldl_of_le
  . intro _ _ _ hs
    exact stepSet_subset le_refl hs
  . suffices nfa.εClosureSet S₁ ⊆ nfa.εClosureSet (nfa.εClosureSet S₂) by
      simp at this
      exact this
    exact εClosureSet_subset le_refl hs

theorem evalFrom_subset {nfa₁ nfa₂ : NFA} {S₁ S₂ : Set Nat} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.evalFrom S₁ s ⊆ nfa₂.evalFrom S₂ s := by
  apply le_foldl_of_le
  . intro _ _ _ hs
    exact stepSet_subset hn hs
  . exact εClosureSet_subset hn hs

theorem mem_evalFrom_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : next ∈ nfa₁.evalFrom S s) :
  next ∈ nfa₂.evalFrom S s :=
  evalFrom_subset le Subset.rfl h

-- Proof of the main result

theorem evalFrom_of_matches.group {s : String} (eq : pushRegex nfa next (.group i r) = nfa')
  (ih : ∀ {nfa next} {nfa'}, pushRegex nfa next r = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s.data) :
  next.val ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data := by
  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property _ _ eq₁ eq₂ eq₃ eq
  rw [eq]
  simp
  have := ih eq₂.symm nfa'' le_refl
  have : nfa'.val.start.val ∈ nfa'''.val.evalFrom {nfa''.val.start.val} s.data := by
    apply mem_evalFrom_le ?_ this
    rw [eq₃]
    apply le_pushNode
  have : nfa'.val.start.val ∈ nfa'''.val.evalFrom {nfa'''.val.start.val} s.data := by
    apply mem_of_mem_of_subset this
    unfold evalFrom
    apply foldl_stepSet_subset_of_le le_refl
    simp [εClosureSet]
    apply subset_εClosure_of_mem
    apply εClosure.step ?_ .base
    rw [eq₃]
    simp [εStep, Node.εStep]
  suffices h : next.val ∈ nfa'''.val.εClosureSet {nfa'.val.start.val} by
    apply mem_of_mem_of_subset h
    apply εClosureSet_subset_foldl_stepSet
    simp
    exact this
  have isLt'' : nfa'.val.start.val < nfa''.val.nodes.size :=
    calc
      _ < nfa'.val.nodes.size := nfa'.val.start.isLt
      _ < nfa''.val.nodes.size := nfa''.property
  have isLt''' : nfa'.val.start.val < nfa'''.val.nodes.size :=
    Nat.lt_trans isLt'' nfa'''.property
  have : nfa'''.val[nfa'.val.start.val] = .save (2 * i + 1) next.val := by
    simp [eq₃]
    rw [pushNode_get_lt _ isLt'']
    rw [pushRegex_get_lt eq₂.symm _ nfa'.val.start.isLt]
    rw [eq₁]
    simp
  simp [εClosureSet]
  apply εClosure.step ?_ .base
  simp [εStep, Node.εStep, this, isLt''']

theorem evalFrom_of_matches.alternateLeft {s : String} (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (ih : ∀ {nfa next} {nfa'}, pushRegex nfa next r₁ = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s.data) :
  next.val ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ eq₂ eq₃ _ eq₅ eq
  rw [eq]
  simp
  have := ih eq₁.symm nfa₁ le_refl
  apply mem_of_mem_of_subset this
  unfold evalFrom
  have le : nfa₁.val ≤ nfa'.val :=
    calc nfa₁.val
      _ ≤ nfa₂.val := eq₃ ▸ le_pushRegex
      _ ≤ nfa' := eq₅ ▸ le_pushNode
  apply foldl_stepSet_subset_of_le le
  calc nfa₁.val.εClosureSet {nfa₁.val.start.val}
    _ ⊆ nfa'.val.εClosureSet {nfa₁.val.start.val} := εClosureSet_subset le Subset.rfl
    _ ⊆ nfa'.val.εClosureSet {nfa'.val.start.val} := by
      simp [εClosureSet]
      have mem : nfa₁.val.start.val ∈ nfa'.val.εClosure nfa'.val.start := by
        rw [eq₅]
        refine εClosure.step ?_ .base
        simp [εStep, Node.εStep, eq₂]
      apply subset_εClosure_of_mem mem

theorem evalFrom_of_matches.alternateRight {s : String} (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (ih : ∀ {nfa next} {nfa'}, pushRegex nfa next r₂ = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s.data) :
  next.val ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property _ _ eq₃ eq₄ eq₅ eq
  rw [eq]
  simp
  have := ih eq₃.symm nfa₂ le_refl
  apply mem_of_mem_of_subset this
  unfold evalFrom
  have le : nfa₂.val ≤ nfa'.val := eq₅ ▸ le_pushNode
  apply foldl_stepSet_subset_of_le le
  calc nfa₂.val.εClosureSet {nfa₂.val.start.val}
    _ ⊆ nfa'.val.εClosureSet {nfa₂.val.start.val} := εClosureSet_subset le Subset.rfl
    _ ⊆ nfa'.val.εClosureSet {nfa'.val.start.val} := by
      simp [εClosureSet]
      intro i h
      have mem : nfa₂.val.start.val ∈ nfa'.val.εClosure nfa'.val.start := by
        rw [eq₅]
        refine εClosure.step ?_ .base
        simp [εStep, Node.εStep, eq₄]
      exact εClosure_trans mem h

theorem evalFrom_of_matches.concat {s s₁ s₂ : String} (eq : pushRegex nfa next (.concat r₁ r₂) = nfa')
  (eqs : s = s₁ ++ s₂)
  (ih₁ : ∀ {nfa next} {nfa'}, pushRegex nfa next r₁ = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s₁.data)
  (ih₂ : ∀ {nfa next} {nfa'}, pushRegex nfa next r₂ = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s₂.data) :
  next.val ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data := by
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq
  rw [eq]
  simp
  unfold evalFrom
  simp [eqs]
  apply mem_of_mem_of_subset (ih₂ eq₂.symm nfa₂ le_refl)
  calc nfa₂.val.evalFrom {nfa₂.val.start.val} s₂.data
    _ ⊆ nfa₁.val.evalFrom {nfa₂.val.start.val} s₂.data :=
      evalFrom_subset (eq₁ ▸ le_pushRegex) Subset.rfl
    _ ⊆ _ := by
      unfold evalFrom
      apply foldl_stepSet_subset_of_le le_refl
      apply εClosureSet_subset_foldl_stepSet
      simp
      exact ih₁ eq₁.symm nfa₁ le_refl

theorem evalFrom_of_matches.starConcat {s s₁ s₂ : String} (eq : pushRegex nfa next (.star r) = nfa')
  (eqs : s = s₁ ++ s₂)
  (ih₁ : ∀ {nfa next} {nfa'}, pushRegex nfa next r = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s₁.data)
  (ih₂ : ∀ {nfa next} {nfa'}, pushRegex nfa next (.star r) = nfa' → ∀ (nfa'' : NFA), nfa' ≤ nfa'' →
    next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s₂.data) :
  next.val ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data := by
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq'
  rw [eq']
  simp [eqs, evalFrom]
  have ih₂ := ih₂ eq nfa' (by simp [eq'])
  unfold evalFrom at ih₂
  apply mem_of_mem_of_subset ih₂
  apply foldl_stepSet_subset_of_le le_refl
  apply εClosureSet_subset_foldl_stepSet
  rw [eq']
  simp
  have : compiled.val ≤ nfa' := by
    intro i
    have : i < nfa'.nodes.size := by
      rw [eq₄]
      simp [eq₃]
    exists this
    simp [eq₄, get_eq_nodes_get]
    simp [eq₃, Array.get_set]
    split
    case inl eq =>
      conv =>
        lhs
        simp [eq₂, ←eq, ←get_eq_nodes_get]
        simp [pushRegex_get_lt rfl _ placeholder.property]
      simp [eq₁]
    case inr _ => simp
  have ih₁ := ih₁ eq₂.symm nfa' this
  simp [evalFrom] at ih₁
  have : nfa'.start.val = nfa.nodes.size := by
    rw [eq₄]
  rw [this]
  apply mem_of_mem_of_subset ih₁
  apply foldl_stepSet_subset_of_le le_refl
  simp [εClosureSet]
  intro i h
  apply εClosure_trans (.step ?_ .base) h
  simp [eq₄, εStep, isLt, get_eq_nodes_get]
  simp [eq₃]
  rw [Array.get_set_eq]
  simp [Node.εStep]

theorem evalFrom_of_matches (eq : pushRegex nfa next r = nfa')
  (m : r.matches s) :
  ∀ nfa'' : NFA, nfa' ≤ nfa'' → next.val ∈ nfa''.evalFrom {nfa'.val.start.val} s.data := by
  induction m generalizing next nfa with
  | @sparse str int char p_in eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, stepSet]
    refine ⟨nfa'.val.start.val, by simp, ?_⟩
    simp [εClosureSet]
    refine ⟨next.val, ?_, .base⟩
    rw [←eq]
    simp [charStep]
    simp [pushRegex, Node.charStep, p_in]
  | @char s c eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, stepSet]
    refine ⟨nfa'.val.start.val, by simp, ?_⟩
    simp [εClosureSet]
    refine ⟨next.val, ?_, .base⟩
    rw [←eq]
    simp [charStep]
    simp [pushRegex, Node.charStep]
  | @epsilon s eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, εClosureSet]
    refine .step ?_ .base
    rw [←eq]
    simp [εStep, pushRegex, Node.εStep]
  | group _ ih =>
    intro nfa'' le
    apply mem_evalFrom_le le
    exact evalFrom_of_matches.group eq ih
  | alternateLeft _ ih =>
    intro nfa'' le
    apply mem_evalFrom_le le
    exact evalFrom_of_matches.alternateLeft eq ih
  | alternateRight _ ih =>
    intro nfa'' le
    apply mem_evalFrom_le le
    exact evalFrom_of_matches.alternateRight eq ih
  | concat s s₁ s₂ r₁ r₂ eqs _ _ ih₁ ih₂ =>
    intro nfa'' le
    apply mem_evalFrom_le le
    exact evalFrom_of_matches.concat eq eqs ih₁ ih₂
  | starEpsilon eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      _ _ eq₃ eq₄ eq
    rw [eq, eqs]
    simp [evalFrom, εClosureSet]
    apply εClosure.step ?_ .base
    rw [eq₄]
    simp [εStep, isLt, get_eq_nodes_get]
    simp [eq₃]
    rw [Array.get_set_eq]
    simp [Node.εStep]
  | starConcat s s₁ s₂ r eqs _ _ ih₁ ih₂ =>
    intro nfa'' le
    apply mem_evalFrom_le le
    exact evalFrom_of_matches.starConcat eq eqs ih₁ ih₂

theorem pathToNext_of_matches_prefix.group {s p s' : String}
  (eq : pushRegex nfa next (.group i r) = nfa')
  (h : s = p ++ s')
  (ih : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next r = nfa' →
    s = p ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data := by
  simp [h]
  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property _ _ eq₁ eq₂ eq₃ eq
  rw [eq]
  simp
  have path₃ : pathToNext nfa' next nfa.nodes.size nfa'.val.start s'.data s'.data := by
    have h₁ : nfa.nodes.size ≤ nfa'.val.start.val := by
      rw [eq₁]
      simp
    refine ⟨nfa'.val.start.val, s'.data, .base h₁ rfl rfl, ?_⟩
    refine .εStep h₁ nfa'.val.start.isLt ?_
    rw [eq₁]
    simp [Node.εStep]
  have path₃ : pathToNext nfa'' next nfa.nodes.size nfa'.val.start s'.data s'.data := by
    apply path₃.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa''.property
    rw [pushRegex_get_lt eq₂.symm _ h₂]
  have path₂ : pathToNext nfa'' nfa'.val.start nfa'.val.nodes.size nfa''.val.start (p.data ++ s'.data) s'.data :=
    ih eq₂.symm rfl
  have path₂ : pathToNext nfa'' nfa'.val.start nfa.nodes.size nfa''.val.start (p.data ++ s'.data) s'.data :=
    path₂.castStart (Nat.le_of_lt nfa'.property)
  have path₂₃ : pathToNext nfa'' next nfa.nodes.size nfa''.val.start (p.data ++ s'.data) s'.data :=
    pathToNext.trans path₂ path₃
  have path₂₃ : pathToNext nfa''' next nfa.nodes.size nfa''.val.start (p.data ++ s'.data) s'.data := by
    apply path₂₃.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa'''.property
    rw [eq₃, pushNode_get_lt _ h₂]
  have path₁ : pathToNext nfa''' nfa''.val.start nfa''.val.nodes.size nfa'''.val.start (p.data ++ s'.data) (p.data ++ s'.data) := by
    have h₁ : nfa''.val.nodes.size ≤ nfa'''.val.start.val := by
      rw [eq₃]
      simp
    refine ⟨nfa'''.val.start, p.data ++ s'.data, .base h₁ rfl rfl, ?_⟩
    refine .εStep h₁ nfa'''.val.start.isLt ?_
    rw [eq₃]
    simp [Node.εStep]
  have path₁ : pathToNext nfa''' nfa''.val.start nfa.nodes.size nfa'''.val.start (p.data ++ s'.data) (p.data ++ s'.data) := by
    apply path₁.castStart (Nat.le_of_lt ?_)
    exact Nat.lt_trans nfa'.property nfa''.property
  exact pathToNext.trans path₁ path₂₃

theorem pathToNext_of_matches_prefix.alternateLeft {s p s' : String}
  (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (h : s = p ++ s')
  (ih : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next r₁ = nfa' →
    s = p ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data := by
  simp [h]
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ eq₂ eq₃ _ eq₅ eq
  rw [eq]
  simp
  have : pathToNext nfa₁ next nfa.nodes.size nfa₁.val.start (p.data ++ s'.data) s'.data
    := ih eq₁.symm rfl
  have : pathToNext nfa' next nfa.nodes.size nfa₁.val.start (p.data ++ s'.data) s'.data
    := by
    apply this.cast
    intro i _ h₂
    have lt₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h₂ nfa₂.property
    have : i < nfa'.val.nodes.size := Nat.lt_trans lt₂ nfa'.property
    exists this
    simp [eq₅]
    rw [pushNode_get_lt _ lt₂]
    rw [pushRegex_get_lt eq₃.symm _ h₂]
  apply this.cons (.εStep ?_ nfa'.val.start.isLt ?_)
  . rw [eq₅]
    simp
    exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
  . rw [eq₅]
    simp [Node.εStep, eq₂]

theorem pathToNext_of_matches_prefix.alternateRight {s p s' : String}
  (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (h : s = p ++ s')
  (ih : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next r₂ = nfa' →
    s = p ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data := by
  simp [h]
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property _ _ eq₃ eq₄ eq₅ eq
  rw [eq]
  simp
  have : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start (p.data ++ s'.data) s'.data
    := (ih eq₃.symm rfl).castStart (Nat.le_of_lt nfa₁.property)
  have : pathToNext nfa' next nfa.nodes.size nfa₂.val.start (p.data ++ s'.data) s'.data
    := by
    apply this.cast
    intro i _ h₂
    have : i < nfa'.val.nodes.size := Nat.lt_trans h₂ nfa'.property
    exists this
    simp [eq₅]
    rw [pushNode_get_lt _ h₂]
  apply this.cons (.εStep ?_ nfa'.val.start.isLt ?_)
  . rw [eq₅]
    simp
    exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
  . rw [eq₅]
    simp [Node.εStep, eq₄]

theorem pathToNext_of_matches_prefix.concat {s p s' p₁ p₂ : String}
  (eq : pushRegex nfa next (.concat r₁ r₂) = nfa')
  (h : s = p ++ s') (eqs : p = p₁ ++ p₂)
  (ih₁ : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next r₁ = nfa' →
    s = p₁ ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data)
  (ih₂ : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next r₂ = nfa' →
    s = p₂ ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data := by
  simp [h, eqs]
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq
  rw [eq]
  simp
  have ih₁ : pathToNext nfa₁ nfa₂.val.start nfa.nodes.size nfa₁.val.start
    (p₁.data ++ (p₂.data ++ s'.data)) (p₂.data ++ s'.data)
    := (ih₁ eq₁.symm rfl).castStart (Nat.le_of_lt nfa₂.property)
  have ih₂ : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start
    (p₂.data ++ s'.data) s'.data
    := ih₂ eq₂.symm rfl
  have ih₂ : pathToNext nfa₁ next nfa.nodes.size nfa₂.val.start
    (p₂.data ++ s'.data) s'.data
    := by
    apply ih₂.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa₁.property
    rw [pushRegex_get_lt eq₁.symm _ h₂]
  exact ih₁.trans ih₂

theorem pathToNext_of_matches_prefix.starConcat {s p s' p₁ p₂ : String}
  (eq : pushRegex nfa next (.star r) = nfa')
  (h : s = p ++ s') (eqs : p = p₁ ++ p₂)
  (ih₁ : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next r = nfa' →
    s = p₁ ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data)
  (ih₂ : ∀ {nfa next nfa'} {s s' : String}, pushRegex nfa next (.star r) = nfa' →
    s = p₂ ++ s' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data := by
  have ih₂ : pathToNext nfa' next nfa.nodes.size nfa'.val.start (p₂.data ++ s'.data) s'.data
    := ih₂ eq rfl
  simp [h, eqs]
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq
  rw [eq]
  simp
  rw [eq] at ih₂
  simp at ih₂
  have eqStart : nfa'.start = nfa.nodes.size := by
    rw [eq₄]
  have ih₁ : pathToNext compiled nfa.nodes.size placeholder.val.nodes.size compiled.val.start
    (p₁.data ++ (p₂.data ++ s'.data)) (p₂.data ++ s'.data) :=
    ih₁ eq₂.symm rfl (s := p₁ ++ (p₂ ++ s'))
  have ih₁ : pathToNext nfa' nfa.nodes.size placeholder.val.nodes.size compiled.val.start
    (p₁.data ++ (p₂.data ++ s'.data)) (p₂.data ++ s'.data) := by
    apply ih₁.cast
    intro i h₁ h₂
    rw [eq₄]
    simp [eq₃]
    exists h₂
    simp [get_eq_nodes_get, eq₃]
    rw [Array.get_set_ne (hj := h₂)]
    simp
    apply Nat.ne_of_lt (Nat.lt_of_lt_of_le placeholder.property h₁)
  have ih₁ : pathToNext nfa' nfa.nodes.size nfa.nodes.size compiled.val.start
    (p₁.data ++ (p₂.data ++ s'.data)) (p₂.data ++ s'.data) :=
    ih₁.castStart (Nat.le_of_lt placeholder.property)
  have ih₂ : pathToNext nfa' next nfa.nodes.size nfa.nodes.size
    (p₂.data ++ s'.data) s'.data := by
    rw [eqStart] at ih₂
    exact ih₂
  have := ih₁.trans ih₂
  apply this.cons (.εStep (by simp [eqStart]) nfa'.start.isLt ?_)
  rw [eq₄]
  simp [get_eq_nodes_get, eq₃]
  rw [Array.get_set_eq]
  simp [Node.εStep]

theorem pathToNext_of_matches_prefix {s p s' : String} (eq : pushRegex nfa next r = nfa')
  (h : s = p ++ s') (m : r.matches p) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start s.data s'.data := by
  induction m generalizing s s' nfa next with
  | @sparse int s c mem eqs =>
    simp [h, eqs]
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨
      nfa'.val.start,
      c :: s'.data,
      .base this rfl rfl,
      .charStep this nfa'.val.start.isLt ?_
    ⟩
    rw [←eq]
    simp [pushRegex, Node.charStep, mem]
  | @char p c eqs =>
    simp [h, eqs]
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨
      nfa'.val.start,
      c :: s'.data,
      .base this rfl rfl,
      .charStep this nfa'.val.start.isLt ?_
    ⟩
    rw [←eq]
    simp [pushRegex, Node.charStep]
  | @epsilon s eqs =>
    simp [h, eqs]
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨nfa'.val.start, s'.data, .base this rfl rfl, .εStep this nfa'.val.start.isLt ?_⟩
    rw [←eq]
    simp [pushRegex, Node.εStep]
  | group _ ih => exact pathToNext_of_matches_prefix.group eq h ih
  | alternateLeft _ ih => exact pathToNext_of_matches_prefix.alternateLeft eq h ih
  | alternateRight _ ih => exact pathToNext_of_matches_prefix.alternateRight eq h ih
  | concat p s₁ s₂ r₁ r₂ eqs _ _ ih₁ ih₂ =>
    exact pathToNext_of_matches_prefix.concat eq h eqs ih₁ ih₂
  | starEpsilon eqs =>
    simp [h, eqs]
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨nfa'.val.start, s'.data, .base this rfl rfl, .εStep this nfa'.val.start.isLt ?_⟩

    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      _ _ eq₃ eq₄ eq

    rw[eq]
    have : nfa'.start.val = nfa.nodes.size := by
      rw [eq₄]
    simp [this, eq₄, get_eq_nodes_get, eq₃]
    rw [Array.get_set_eq]
    simp [Node.εStep]
  | starConcat p s₁ s₂ r eqs _ _ ih₁ ih₂ =>
    exact pathToNext_of_matches_prefix.starConcat eq h eqs ih₁ ih₂

theorem pathToNext_of_compile_matches_prefix (eq : NFA.compile r = nfa)
  (h : s = p ++ s') (m : r.matches p) :
  pathToNext nfa 0 1 nfa.start s.data s'.data := by
  unfold NFA.compile at eq
  set result := NFA.done.pushRegex ⟨0, by decide⟩ r
  have := pathToNext_of_matches_prefix (rfl : result = result) h m
  rw [eq] at this
  exact this

end NFA
