-- When the regex matches a string, the compiled NFA accepts it.
import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Order
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
      intro i h
      have mem : nfa₁.val.start.val ∈ nfa'.val.εClosure nfa'.val.start := by
        rw [eq₅]
        refine εClosure.step ?_ .base
        simp [εStep, Node.εStep, eq₂]
      exact εClosure_trans mem h

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
  | @char s c eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, stepSet]
    refine ⟨nfa'.val.start.val, by simp, ?_⟩
    simp [εClosureSet]
    refine ⟨next.val, ?_, .base⟩
    rw [←eq]
    simp [charStep, pushRegex, Node.charStep]
  | @epsilon s eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, εClosureSet]
    refine .step ?_ .base
    rw [←eq]
    simp [εStep, pushRegex, Node.εStep]
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

end NFA
