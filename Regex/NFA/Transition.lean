import Regex.Lemmas
import Regex.NFA.Basic
import Regex.NFA.Compile

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

open Set

-- TODO: we may want to prove that all indices are in bounds get rid of Option helpers.
def Option.charStep : Option NFA.Node → Char → Set Nat
  | some n, c => n.charStep c
  | none, _ => ∅

def Option.εStep : Option NFA.Node → Set Nat
  | some n => n.εStep
  | none => ∅

namespace NFA

def Option.charStep.simp {nfa : NFA} {i : Nat} {c : Char} :
  nfa[i]?.charStep c = if h : i < nfa.nodes.size then nfa[i].charStep c else ∅ := by
  simp [Option.charStep, getElem?]
  cases Nat.decLt i nfa.nodes.size <;> simp [*]

theorem Option.charStep.subset_of_le {nfa₁ nfa₂ : NFA} {i : Nat} (le : nfa₁ ≤ nfa₂) :
  nfa₁[i]?.charStep c ⊆ nfa₂[i]?.charStep c := by
  simp [Option.charStep.simp]
  cases Nat.decLt i nfa₁.nodes.size <;> simp [*]
  case isTrue h =>
    let ⟨h', le⟩ := le i h
    simp [h']
    exact le.left c

def Option.εStep.simp {nfa : NFA} {i : Nat} :
  nfa[i]?.εStep = if h : i < nfa.nodes.size then nfa[i].εStep else ∅ := by
  simp [Option.εStep, getElem?]
  cases Nat.decLt i nfa.nodes.size <;> simp [*]

theorem Option.εStep.subset_of_le {nfa₁ nfa₂ : NFA} {i : Nat} (le : nfa₁ ≤ nfa₂) :
  nfa₁[i]?.εStep ⊆ nfa₂[i]?.εStep := by
  simp [Option.εStep.simp]
  cases Nat.decLt i nfa₁.nodes.size <;> simp [*]
  case isTrue h =>
    let ⟨h', le⟩ := le i h
    simp [h']
    exact le.right

inductive NFA.εClosure (nfa : NFA) : Nat → Set Nat where
  | base : εClosure nfa i i
  | step {i j k : Nat} (head : j ∈ nfa[i]?.εStep) (tail : nfa.εClosure j k) :
    εClosure nfa i k

theorem εClosure_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : j ∈ nfa₁.εClosure i) :
  j ∈ nfa₂.εClosure i := by
  induction h with
  | base => exact .base
  | step head _ ih => exact .step (mem_of_subset_of_mem (Option.εStep.subset_of_le le) head) ih

theorem εClosure_trans {nfa : NFA} (h₁ : i₂ ∈ nfa.εClosure i₁) (h₂ : i₃ ∈ nfa.εClosure i₂) :
  i₃ ∈ nfa.εClosure i₁ := by
  induction h₁ with
  | base => exact h₂
  | step head _ ih => exact .step head (ih h₂)

def NFA.εClosureSet (nfa : NFA) (S : Set Nat) : Set Nat
  | j => ∃ i ∈ S, j ∈ nfa.εClosure i

@[simp]
theorem subset_εClosureSet {nfa : NFA} : S ⊆ nfa.εClosureSet S := by
  intro i h
  exists i
  exact ⟨h, .base⟩

@[simp]
theorem εClosureSet_singleton_base {nfa : NFA} : i ∈ nfa.εClosureSet {i} := by
  exists i
  exact ⟨mem_singleton _, .base⟩

@[simp]
theorem εClosureSet_singleton_step {nfa : NFA} {i j : Nat} (h : j ∈ nfa[i]?.εStep) : j ∈ nfa.εClosureSet {i} := by
  exists i
  exact ⟨mem_singleton _, .step h .base⟩

@[simp]
theorem εClosureSet_empty {nfa : NFA} : nfa.εClosureSet ∅ = ∅ := by
  apply eq_empty_of_forall_not_mem
  intro i h
  induction h with
  | intro _ h => apply not_mem_empty _ h.left

@[simp]
theorem εClosureSet_univ {nfa : NFA} : nfa.εClosureSet univ = univ := by
  apply eq_univ_of_forall
  intro i
  exists i
  exact ⟨mem_univ _, .base⟩

theorem εClosureSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.εClosureSet S₁ ⊆ nfa₂.εClosureSet S₂ := by
  simp [subset_def]
  intro j h
  let ⟨i, h, cls⟩ := h
  exact ⟨i, mem_of_subset_of_mem hs h, εClosure_of_le hn cls⟩

@[simp]
theorem εClosureSet_idempotent {nfa : NFA} : nfa.εClosureSet (nfa.εClosureSet S) = nfa.εClosureSet S := by
  apply eq_of_subset_of_subset
  . simp [subset_def]
    intro j h
    let ⟨i, h, cls⟩ := h
    let ⟨i', h', cls'⟩ := h
    exact ⟨i', h', εClosure_trans cls' cls⟩
  . apply subset_εClosureSet

theorem εClosureSet_iUnion_distrib {nfa : NFA} {S : Set α} {f : α → Set Nat} :
  nfa.εClosureSet (⋃ i ∈ S, f i) = ⋃ i ∈ S, nfa.εClosureSet (f i) := by
  sorry

def NFA.stepSet (nfa : NFA) (S : Set Nat) (c : Char) : Set Nat :=
  ⋃ i ∈ S, nfa.εClosureSet (nfa[i]?.charStep c)

@[simp]
def stepSet_empty {nfa : NFA} : nfa.stepSet ∅ c = ∅ := by
  simp [NFA.stepSet]

-- @[simp]
-- def mem_stepSet_iff {nfa : NFA} : j ∈ nfa.stepSet S c ↔ ∃ i ∈ S, j ∈ nfa.εClosureSet (nfa[i]?.charStep c) := by
--   apply Iff.intro
--   . intro h; exact h
--   . intro h; exact h

@[simp]
theorem εClosureSet_stepSet {nfa : NFA} :
  nfa.εClosureSet (nfa.stepSet S c) = nfa.stepSet S c := by
  apply eq_of_subset_of_subset
  . conv =>
      lhs
      simp [NFA.stepSet, εClosureSet_iUnion_distrib]
  . exact subset_εClosureSet

theorem stepSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.stepSet S₁ c ⊆ nfa₂.stepSet S₂ c := by
  simp [subset_def, NFA.stepSet]
  intro j i h₁ h₂

  exact ⟨
    i,
    mem_of_subset_of_mem hs h₁,
    mem_of_subset_of_mem (εClosureSet_subset hn (Option.charStep.subset_of_le hn)) h₂
  ⟩

def NFA.evalFrom (nfa : NFA) (S : Set Nat) : List Char → Set Nat :=
  List.foldl (nfa.stepSet) (nfa.εClosureSet S)

theorem evalFrom_cons {nfa : NFA} :
  nfa.evalFrom S (c :: cs) = nfa.evalFrom (nfa.stepSet (nfa.εClosureSet S) c) cs := by
  have h : nfa.stepSet (nfa.εClosureSet S) c = nfa.εClosureSet (nfa.stepSet (nfa.εClosureSet S) c) :=
    εClosureSet_stepSet.symm
  conv =>
    lhs
    simp [NFA.evalFrom]
    rw [h]

theorem evalFrom_subset {nfa₁ nfa₂ : NFA} {S₁ S₂ : Set Nat} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.evalFrom S₁ s ⊆ nfa₂.evalFrom S₂ s := by
  apply le_foldl_of_le
  . intro _ _ _ hs
    exact stepSet_subset hn hs
  . exact εClosureSet_subset hn hs

theorem εClosureSet_evalFrom {nfa : NFA} :
  nfa.εClosureSet (nfa.evalFrom S s) = nfa.evalFrom S s := by
  apply eq_of_subset_of_subset
  . induction s generalizing S with
    | nil => simp [NFA.evalFrom]; exact le_refl _
    | cons c cs ih =>
      rw [evalFrom_cons]
      exact ih
  . exact subset_εClosureSet

theorem mem_evalFrom_subset {nfa : NFA} (hmem : next ∈ nfa.evalFrom S₁ s) (hs : S₁ ⊆ nfa.εClosureSet S₂) :
  next ∈ nfa.evalFrom S₂ s := by
  apply mem_of_subset_of_mem _ hmem
  apply le_foldl_of_le
  . intro _ _ _ hs
    exact stepSet_subset (le_refl _) hs
  . suffices nfa.εClosureSet S₁ ⊆ nfa.εClosureSet (nfa.εClosureSet S₂) by
      simp at this
      exact this
    exact εClosureSet_subset (le_refl _) hs

theorem evalFrom_append {nfa : NFA} (eq : s = s₁ ++ s₂) :
  nfa.evalFrom S s = List.foldl (nfa.stepSet) (nfa.evalFrom S s₁) s₂ := by
  conv =>
    lhs
    rw [eq, NFA.evalFrom, List.foldl_append]

theorem NFA.evalFrom_of_matches (eq : compile.loop r next nfa = nfa')
  (m : r.matches s) : ∀ nfa'' : NFA, nfa' ≤ nfa'' → next ∈ nfa''.evalFrom {nfa'.val.start.val} s.data := by
  induction m generalizing next nfa with
  | @char s c eqs =>
    intro nfa'' le
    suffices next ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data from
      evalFrom_subset le (le_refl _) this
    simp [eqs, evalFrom, List.foldl]
    simp [compile.loop] at eq
    apply mem_iUnion.mpr
    exists nfa'.val.start
    subst eq
    simp [Option.charStep, Node.charStep]
  | @epsilon s eqs =>
    intro nfa'' le
    suffices next ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data from
      evalFrom_subset le (le_refl _) this
    simp [eqs, evalFrom, List.foldl]
    simp [compile.loop] at eq
    exists nfa'.val.start
    subst eq
    simp [Option.charStep, Node.charStep]
    exact εClosure.step (by simp [Option.εStep, Node.εStep]) .base
  | @alternateLeft s r₁ r₂ m ih =>
    intro nfa'' le
    suffices next ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data from
      evalFrom_subset le (le_refl _) this

    let nfa₁ := compile.loop r₁ next nfa
    let start₁ := nfa₁.val.start
    let nfa₂ := compile.loop r₂ next nfa₁
    let start₂ := nfa₂.val.start
    let final := nfa₂.val.addNode (.split start₁ start₂)

    have : nfa'.val = final.val := by
      simp [eq.symm]
      rfl
    rw [this]

    have property : nfa₁.val ≤ final.val :=
      calc nfa₁.val
        _ ≤ nfa₂.val := nfa₂.property
        _ ≤ final.val := final.property

    apply mem_evalFrom_subset (ih rfl final property)
    simp [Option.εStep, Node.εStep]
  | @alternateRight s r₁ r₂ m ih =>
    intro nfa'' le
    suffices next ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data from
      evalFrom_subset le (le_refl _) this

    let nfa₁ := compile.loop r₁ next nfa
    let start₁ := nfa₁.val.start
    let nfa₂ := compile.loop r₂ next nfa₁
    let start₂ := nfa₂.val.start
    let final := nfa₂.val.addNode (.split start₁ start₂)

    have : nfa'.val = final.val := by
      simp [eq.symm]
      rfl
    rw [this]

    apply mem_evalFrom_subset (ih rfl final final.property)
    simp [Option.εStep, Node.εStep]
  | concat s s₁ s₂ r₁ r₂ eqs m₁ m₂ ih₁ ih₂ =>
    intro nfa'' le
    suffices next ∈ nfa'.val.evalFrom {nfa'.val.start.val} s.data from
      evalFrom_subset le (le_refl _) this

    let nfa₂ := compile.loop r₂ next nfa
    let nfa₁ := compile.loop r₁ nfa₂.val.start nfa₂

    have : nfa'.val = nfa₁.val := by
      simp [eq.symm]
      rfl
    rw [this]

    let ih₁ := ih₁ rfl nfa₁ (le_refl _)
    let ih₂ := ih₂ rfl nfa₁ nfa₁.property

    apply mem_of_mem_of_subset ih₂
    show nfa₁.val.evalFrom {nfa₂.val.start.val} s₂.data ⊆ nfa₁.val.evalFrom {nfa₁.val.start.val} s.data
    rw [evalFrom_append (String.eq_of_append_of_eq_of_append eqs)]
    apply le_foldl_of_le
    . intro _ _ _ hs
      exact stepSet_subset (le_refl _) hs
    . have : {nfa₂.val.start.val} ⊆ nfa₁.val.evalFrom {nfa₁.val.start.val} s₁.data := by
        rw [singleton_subset_iff]
        exact ih₁
      have : nfa₁.val.εClosureSet {nfa₂.val.start.val} ⊆ nfa₁.val.εClosureSet (nfa₁.val.evalFrom {nfa₁.val.start.val} s₁.data) :=
        εClosureSet_subset (le_refl _) this
      rw [εClosureSet_evalFrom] at this
      exact this
  | star m ih => sorry

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

end NFA
