import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Transition.AcceptOfMatch
import RegexCorrectness.Lemmas

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

open Set

---------- When the regex matches a string, the compiled NFA accepts it.

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

theorem εClosure_subset_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) :
  nfa₁.εClosure i ⊆ nfa₂.εClosure i := by
  intro j h
  exact εClosure_of_le le h

theorem εClosure_snoc {nfa : NFA} (h : j < nfa.nodes.size)
  (cls : j ∈ nfa.εClosure i) (step : k ∈ nfa[j].εStep) :
  k ∈ nfa.εClosure i := by
  induction cls with
  | @base i =>
    exact .step (by rw [getElem?_pos nfa i h]; simp [Option.εStep, step] ) .base
  | step step' _ ih =>
    have ih := ih h step
    exact NFA.εClosure.step step' ih

theorem εClosure_trans {nfa : NFA} (h₁ : i₂ ∈ nfa.εClosure i₁) (h₂ : i₃ ∈ nfa.εClosure i₂) :
  i₃ ∈ nfa.εClosure i₁ := by
  induction h₁ with
  | base => exact h₂
  | step head _ ih => exact .step head (ih h₂)

theorem lt_of_inBounds_of_εClosure {nfa : NFA} (inBounds : nfa.inBounds)
  (h : i < nfa.nodes.size) (cls : j ∈ nfa.εClosure i) :
  j < nfa.nodes.size := by
  induction cls with
  | @base i => exact h
  | @step i j _ mem _ ih =>
    simp [getElem?_pos nfa i h, Option.εStep] at mem
    have : j < nfa.nodes.size := lt_of_inBounds_of_εStep inBounds mem
    exact ih this

def NFA.εClosureSet (nfa : NFA) (S : Set Nat) : Set Nat :=
  ⋃ i ∈ S, nfa.εClosure i

@[simp]
theorem subset_εClosureSet {nfa : NFA} : S ⊆ nfa.εClosureSet S := by
  intro i h
  apply mem_iUnion_of_mem i
  simp
  exact ⟨h, .base⟩

@[simp]
theorem εClosureSet_singleton_base {nfa : NFA} : i ∈ nfa.εClosureSet {i} := by
  apply mem_iUnion_of_mem i
  simp
  exact .base

@[simp]
theorem εClosureSet_singleton_step {nfa : NFA} {i j : Nat} (h : j ∈ nfa[i]?.εStep) : j ∈ nfa.εClosureSet {i} := by
  apply mem_iUnion_of_mem i
  simp
  exact .step h .base

@[simp]
theorem εClosureSet_singleton {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i):
  j ∈ nfa.εClosureSet {i} := by
  apply mem_iUnion_of_mem i
  simp [h]

@[simp]
theorem εClosureSet_empty {nfa : NFA} : nfa.εClosureSet ∅ = ∅ := by
  simp [NFA.εClosureSet]

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
    simp [mem_iUnion, NFA.εClosureSet] at h
    let ⟨i, h, j, cls, cls'⟩ := h
    exact mem_iUnion_of_mem i (mem_iUnion_of_mem h (εClosure_trans cls cls'))
  . apply subset_εClosureSet

theorem εClosureSet_iUnion_distrib {nfa : NFA} {S : Set α} {f : α → Set Nat} :
  nfa.εClosureSet (⋃ i ∈ S, f i) = ⋃ i ∈ S, nfa.εClosureSet (f i) := by
  simp [NFA.εClosureSet]

theorem εClosureSet_union_distrib {nfa : NFA} {S₁ S₂ : Set Nat} :
  nfa.εClosureSet (S₁ ∪ S₂) = nfa.εClosureSet S₁ ∪ nfa.εClosureSet S₂ := by
  apply eq_of_subset_of_subset
  . simp [subset_def]
    intro j h
    simp [NFA.εClosureSet] at *
    let ⟨i, h, cls⟩ := h
    cases h with
    | inl h => exact .inl ⟨i, h, cls⟩
    | inr h => exact .inr ⟨i, h, cls⟩
  . simp [subset_def]
    intro j h
    simp [NFA.εClosureSet] at *
    cases h with
    | inl h =>
      let ⟨i, h, cls⟩ := h
      exact ⟨i, .inl h, cls⟩
    | inr h =>
      let ⟨i, h, cls⟩ := h
      exact ⟨i, .inr h, cls⟩

def NFA.stepSet (nfa : NFA) (S : Set Nat) (c : Char) : Set Nat :=
  ⋃ i ∈ S, nfa.εClosureSet (nfa[i]?.charStep c)

@[simp]
def stepSet_empty {nfa : NFA} : nfa.stepSet ∅ c = ∅ := by
  simp [NFA.stepSet]

@[simp]
theorem εClosureSet_stepSet {nfa : NFA} :
  nfa.εClosureSet (nfa.stepSet S c) = nfa.stepSet S c := by
  apply eq_of_subset_of_subset
  . conv =>
      lhs
      simp [NFA.stepSet, εClosureSet_iUnion_distrib]
  . exact subset_εClosureSet

theorem stepSet_union_distrib {nfa : NFA} {S₁ S₂ : Set Nat} :
  nfa.stepSet (S₁ ∪ S₂) c = nfa.stepSet S₁ c ∪ nfa.stepSet S₂ c := by
  simp [NFA.stepSet, εClosureSet_union_distrib]
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

theorem lt_of_inBounds_of_stepSet {nfa : NFA} (inBounds : nfa.inBounds)
  (mem : j ∈ nfa.stepSet S c) : j < nfa.nodes.size := by
  simp [NFA.stepSet] at mem
  let ⟨i, _, cls⟩ := mem
  cases Nat.decLt i nfa.nodes.size with
  | isTrue lt =>
    simp [getElem?_pos nfa i lt, Option.charStep] at cls
    simp [NFA.εClosureSet] at cls
    let ⟨i', mem', cls'⟩ := cls
    have : i' < nfa.nodes.size := lt_of_inBounds_of_charStep inBounds mem'
    exact lt_of_inBounds_of_εClosure inBounds this cls'
  | isFalse nlt => simp [getElem?_neg nfa i nlt, Option.charStep] at cls

theorem stepSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
  nfa₁.stepSet S₁ c ⊆ nfa₂.stepSet S₂ c := by
  simp [subset_def, NFA.stepSet]
  intro j i h₁ h₂

  exact ⟨
    i,
    mem_of_subset_of_mem hs h₁,
    mem_of_subset_of_mem (εClosureSet_subset hn (Option.charStep.subset_of_le hn)) h₂
  ⟩

theorem foldl_stepSet_subset {nfa : NFA} (h : S₁ ⊆ S₂) :
  List.foldl (nfa.stepSet) S₁ cs ⊆ List.foldl (nfa.stepSet) S₂ cs := by
  induction cs generalizing S₁ S₂ with
  | nil => simp [h]
  | cons c _ ih =>
    simp
    apply ih
    exact stepSet_subset (le_refl _) h

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

theorem mem_evalFrom_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : next ∈ nfa₁.evalFrom S s) :
  next ∈ nfa₂.evalFrom S s :=
  evalFrom_subset le (le_refl _) h

theorem evalFrom_of_matches (eq : compile.loop r next nfa = nfa')
  (m : r.matches s) : ∀ nfa'' : NFA, nfa' ≤ nfa'' → next ∈ nfa''.evalFrom {nfa'.val.start.val} s.data := by
  induction m generalizing next nfa with
  | @char s c eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, NFA.evalFrom, List.foldl]
    simp [compile.loop] at eq
    apply mem_iUnion_of_mem nfa'.val.start.val
    subst eq
    simp [Option.charStep, Node.charStep]
  | @epsilon s eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, NFA.evalFrom, List.foldl]
    simp [compile.loop] at eq
    apply mem_iUnion_of_mem nfa'.val.start.val
    subst eq
    simp [Option.charStep, Node.charStep]
    exact NFA.εClosure.step (by simp [Option.εStep, Node.εStep]) .base
  | @alternateLeft s r₁ r₂ _ ih =>
    intro nfa'' le
    apply mem_evalFrom_le le

    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ eq₃ _ eq₅ eq

    have property : nfa₁.val ≤ final.val :=
      calc nfa₁.val
        _ ≤ nfa₂.val := eq₃ ▸ NFA.compile.loop.le
        _ ≤ final.val := eq₅ ▸ NFA.le_addNode

    rw [eq]
    simp

    apply mem_evalFrom_subset (ih eq₁.symm final property)
    simp
    apply εClosureSet_singleton_step
    rw [eq₅]
    simp [Option.εStep, Node.εStep]
    exact .inl (by rw [eq₂])
  | @alternateRight s r₁ r₂ _ ih =>
    intro nfa'' le
    apply mem_evalFrom_le le

    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ final property _ _ eq₃ eq₄ eq₅ eq

    rw [eq]
    simp

    have : nfa₂.val ≤ final.val := eq₅ ▸ NFA.le_addNode
    apply mem_evalFrom_subset (ih eq₃.symm final this)
    simp
    apply εClosureSet_singleton_step
    rw [eq₅]
    simp [Option.εStep, Node.εStep]
    exact .inr (by rw [eq₄])
  | concat s s₁ s₂ r₁ r₂ eqs _ _ ih₁ ih₂ =>
    intro nfa'' le
    apply mem_evalFrom_le le

    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    rw [eq]
    simp

    let ih₁ := ih₁ eq₁.symm nfa₁ (le_refl _)
    let ih₂ := ih₂ eq₂.symm nfa₁ (eq₁ ▸ compile.loop.le)

    apply mem_of_mem_of_subset ih₂
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
  | starEpsilon eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le

    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      _ _ _ eq₄ eq₅ eq'

    rw [eq']
    simp

    simp [eqs, NFA.evalFrom, NFA.εClosureSet]

    have : nfa'''[nfa'''.start.val] = .split nfa''.val.start next := by
      rw [eq₅, NFA.eq_get]
      simp [eq₄]
    have head : next ∈ nfa'''[nfa'''.start]?.εStep := by
      unfold getElem?
      simp [this, Option.εStep, Node.εStep]
    have tail : next ∈ nfa'''.εClosure next := .base
    exact NFA.εClosure.step head tail
  | starConcat s s₁ s₂ r eqs _ _ ih₁ ih₂ =>
    intro nfa'' le
    apply mem_evalFrom_le le

    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq'

    rw [eq']
    simp

    have eq'' : compile.loop (.star r) next nfa = ⟨nfa''', property'⟩ := by
      rw [eq'] at eq
      exact eq
    have : nfa''.val ≤ nfa''' := by
      intro i h
      have : nodes'''.size = nfa''.val.nodes.size := by
        simp [eq₄]
      have : i < nodes'''.size := by
        simp [this, h]
      have h' : i < nfa'''.nodes.size := by
        simp [eq₅, this]
      exists h'
      cases Nat.decEq start i with
      | isTrue eq =>
        have lhs : nfa''.val[i] = .fail := by
          simp [eq₃, eq.symm]
          have : start.val < nfa'.val.nodes.size := by
            rw [eq₂]
            exact nfa'.val.start.isLt
          simp [compile.loop.get_lt rfl this]
          have : start.val = (nfa.addNode .fail).val.start.val := by
            rw [eq₂, eq₁]
          simp [this, eq₁]
        have rhs : nfa'''[i] = .split nfa''.val.start next := by
          simp [NFA.eq_get, eq₅, eq₄, eq.symm]
        simp [lhs, rhs]
      | isFalse neq =>
        have : nodes'''[i] = nfa''.val.nodes[i] := by
          simp [eq₄]
          apply Array.get_set_ne
          exact neq
        simp [NFA.eq_get, eq₅, this]
    have ih₁ := ih₁ eq₃.symm nfa''' this
    have ih₂ := ih₂ eq'' nfa''' (le_refl _)

    rw [evalFrom_append (String.eq_of_append_of_eq_of_append eqs)]
    suffices next ∈ nfa'''.evalFrom (nfa'''.evalFrom {nfa'''.start.val} s₁.data) s₂.data by
      have : next ∈ List.foldl nfa'''.stepSet (nfa'''.εClosureSet (nfa'''.evalFrom {nfa'''.start.val} s₁.data)) s₂.data := by
        exact this
      simp [εClosureSet_evalFrom] at this
      exact this
    apply mem_evalFrom_subset ih₂
    simp [εClosureSet_evalFrom]

    have : nfa'''.start.val = start.val := by
      rw [eq₅]
    apply mem_evalFrom_subset (this.symm ▸ ih₁)
    simp
    apply εClosureSet_singleton_step
    have : nfa'''[nfa'''.start.val] = .split nfa''.val.start next := by
      rw [eq₅, NFA.eq_get]
      simp [eq₄]
    simp [this, getElem?, Option.εStep, Node.εStep]

---------- When the NFA accepts a string, it matches the original regex.

inductive NFA.stepIn (nfa : NFA) (start : Nat) : Nat → List Char → Nat → List Char → Prop where
  | charStep {i j : Nat} {c : Char} {cs : List Char}
    (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c) :
    nfa.stepIn start i (c :: cs) j cs
  | εStep {i j : Nat} {cs : List Char}
    (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].εStep) :
    nfa.stepIn start i cs j cs

-- TODO: make stepIn a plain structure (with unified step predicate)
-- and have the followings as fields.
theorem NFA.stepIn.h₁ {nfa : NFA} {start : Nat} {i j : Nat} {cs cs' : List Char}
  (step : nfa.stepIn start i cs j cs') : start ≤ i := by
  cases step with
  | charStep h₁ _ _ => exact h₁
  | εStep h₁ _ _ => exact h₁

theorem NFA.stepIn.h₂ {nfa : NFA} {start : Nat} {i j : Nat} {cs cs' : List Char}
  (step : nfa.stepIn start i cs j cs') : i < nfa.nodes.size := by
  cases step with
  | charStep _ h₂ _ => exact h₂
  | εStep _ h₂ _ => exact h₂

theorem le_of_stepIn (step : NFA.stepIn nfa start i cs j cs') : start ≤ i := by
  cases step with
  | charStep h₁ => exact h₁
  | εStep h₁ => exact h₁

theorem NFA.stepIn.lt_of_inBounds {nfa : NFA} {start i j : Nat} {cs cs' : List Char}
  (inBounds : nfa.inBounds) (step : nfa.stepIn start i cs j cs') :
  j < nfa.nodes.size := by
  cases step with
  | charStep _ _ step => exact lt_of_inBounds_of_charStep inBounds step
  | εStep _ _ step => exact lt_of_inBounds_of_εStep inBounds step

theorem NFA.stepIn.castStart' {nfa : NFA} {start start' : Nat}
  (le : start' ≤ i) (step : NFA.stepIn nfa start i cs j cs') :
  nfa.stepIn start' i cs j cs' := by
  cases step with
  | charStep h₁ h₂ step => exact .charStep le h₂ step
  | εStep h₁ h₂ step => exact .εStep le h₂ step

theorem NFA.stepIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start) (step : NFA.stepIn nfa start i cs j cs') :
  nfa.stepIn start' i cs j cs' := step.castStart' (Nat.le_trans le step.h₁)

theorem NFA.stepIn.cast {nfa nfa' : NFA} {start : Nat}
  (step : nfa.stepIn start i cs j cs')
  (h : i < nfa'.nodes.size)
  (eq : nfa[i]'(step.h₂) = nfa'[i]) :
  nfa'.stepIn start i cs j cs' := by
  cases step with
  | charStep h₁ h₂ step =>
    exact .charStep h₁ h (eq ▸ step)
  | εStep h₁ h₂ step =>
    exact .εStep h₁ h (eq ▸ step)

-- Maybe we should recurse from the last as we reason about the last step often
inductive NFA.pathIn (nfa : NFA) (start : Nat) : Nat → List Char → Nat → List Char → Prop where
  | base (h : start ≤ i) (eqi : i = j) (eqs : cs = cs') : nfa.pathIn start i cs j cs'
  | step {i j k : Nat} {cs cs' cs'' : List Char}
    (step : nfa.stepIn start i cs j cs') (rest : nfa.pathIn start j cs' k cs'') :
    nfa.pathIn start i cs k cs''

theorem le_of_pathIn_left (path : NFA.pathIn nfa start i cs j cs') : start ≤ i := by
  cases path with
  | base h => exact h
  | step step _ => exact le_of_stepIn step

theorem le_of_pathIn_right (path : NFA.pathIn nfa start i cs j cs') : start ≤ j := by
  induction path with
  | base h eqi => exact eqi ▸ h
  | step _ _ ih => exact ih

theorem NFA.pathIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start)
  (path : nfa.pathIn start i cs j cs') :
  nfa.pathIn start' i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base (Nat.le_trans le h) eqi eqs
  | step step _ ih => exact .step (step.castStart le) ih

theorem NFA.pathIn.cast {nfa nfa' : NFA} (start : Nat)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : NFA.pathIn nfa start i cs j cs') :
  NFA.pathIn nfa' start i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base h eqi eqs
  | step step _ ih =>
    let ⟨h, eq⟩ := eq _ step.h₁ step.h₂
    exact .step (step.cast h eq) ih

theorem NFA.pathIn.cast' {nfa nfa' : NFA} {start : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (inBounds : ∀ i j, (h : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    j < nfa.nodes.size)
  (path : NFA.pathIn nfa' start i cs j cs') :
  NFA.pathIn nfa start i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base h eqi eqs
  | @step i j k cs cs' cs'' step _ ih =>
    have eq := eq _ step.h₁ assm
    -- TODO: we should embed inBounds to NFA. For now, we perform an ad-hoc case analysis.
    have : j < nfa.nodes.size := by
      cases step with
      | @charStep _ c _ _ _ step => exact inBounds _ _ assm (.inl ⟨c, eq ▸ step⟩)
      | εStep _ _ step => exact inBounds _ _ assm (.inr (eq ▸ step))
    exact .step (step.cast assm eq.symm) (ih this)

theorem NFA.pathIn.castLE {nfa : NFA} {start start' i i' : Nat}
  (assm : start' ≤ i)
  (inBounds : ∀ i j, (h₁ : start' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    start ≤ j →
    start' ≤ j)
  (path : NFA.pathIn nfa start i cs i' cs') :
  NFA.pathIn nfa start' i cs i' cs' := by
  induction path with
  | base _ eqi eqs => exact .base assm eqi eqs
  | @step i j k cs cs' cs'' step rest ih =>
    have h₂ := step.h₂
    have : start' ≤ j := by
      cases step with
      | charStep _ _ step => exact inBounds i j assm h₂ (.inl ⟨_, step⟩) (le_of_pathIn_left rest)
      | εStep _ _ step => exact inBounds i j assm h₂ (.inr step) (le_of_pathIn_left rest)
    exact .step (step.castStart' assm) (ih this)

theorem NFA.pathIn.lt_of_lt {nfa : NFA} {start i i' : Nat}
  (assm : i < n)
  (inBounds : ∀ i j, (h : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    j < n)
  (path : NFA.pathIn nfa start i cs i' cs') :
  i' < n := by
  induction path with
  | base _ eqi _ => exact eqi ▸ assm
  | @step i j _ _ _ _ step _ ih =>
    have : j < n := by
      cases step with
      | @charStep _ c _ _ h₂ step => exact inBounds i j h₂ (.inl ⟨c, step⟩)
      | εStep _ h₂ step => exact inBounds i j h₂ (.inr step)
    exact ih this

theorem NFA.pathIn.snoc_char {start}
  (assm₁ : j < nfa.nodes.size) (assm₂ : cs' = c :: cs'')
  (step : k ∈ nfa[j].charStep c) (path : NFA.pathIn nfa start i cs j cs')
  : NFA.pathIn nfa (min start k) i cs k cs'' := by
  induction path with
  | base h eqi eqs =>
    subst eqi eqs assm₂
    exact .step (.charStep (Nat.le_trans (Nat.min_le_left _ _) h) assm₁ step) (.base (Nat.min_le_right _ _) rfl rfl)
  | step step' rest ih =>
    have ih := ih assm₁ assm₂ step
    exact .step (step'.castStart (Nat.min_le_left _ _)) ih

theorem NFA.pathIn.snoc_ε {start}
  (assm : j < nfa.nodes.size)
  (step : k ∈ nfa[j].εStep) (path : NFA.pathIn nfa start i cs j cs')
  : NFA.pathIn nfa (min start k) i cs k cs' := by
  induction path with
  | base h eqi eqs =>
    subst eqi eqs
    exact .step (.εStep (Nat.le_trans (Nat.min_le_left _ _) h) assm step) (.base (Nat.min_le_right _ _) rfl rfl)
  | step step' rest ih =>
    have ih := ih assm step
    exact .step (step'.castStart (Nat.min_le_left _ _)) ih

theorem NFA.pathIn.trans {start}
  (path₁ : NFA.pathIn nfa start i cs j cs') (path₂ : NFA.pathIn nfa start j cs' k cs'') :
  NFA.pathIn nfa start i cs k cs'' := by
  induction path₁ with
  | base _ eqi eqs => exact eqi ▸ eqs ▸ path₂
  | step step _ ih => exact .step step (ih path₂)

def NFA.pathToNext (nfa : NFA) (next start i : Nat) (cs cs' : List Char) : Prop :=
  ∃ (i' : Nat) (cs'' : List Char),
    nfa.pathIn start i cs i' cs'' ∧
    nfa.stepIn start i' cs'' next cs'

theorem le_of_pathToNext (path : NFA.pathToNext nfa next start i cs cs') : start ≤ i := by
  obtain ⟨_, _, path, _⟩ := path
  exact le_of_pathIn_left path

theorem NFA.pathToNext.cons {start} {cs cs' cs'' : List Char}
  (step : stepIn nfa start i cs j cs') (path : pathToNext nfa next start j cs' cs'') :
  pathToNext nfa next start i cs cs'' := by
  obtain ⟨i', cs''', path, step'⟩ := path
  exact ⟨i', cs''', .step step path, step'⟩

theorem NFA.pathToNext.cast {nfa nfa' : NFA} {next start i : Nat} {cs cs' : List Char}
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : NFA.pathToNext nfa next start i cs cs') :
  NFA.pathToNext nfa' next start i cs cs' := by
  obtain ⟨i', cs'', path, step⟩ := path
  obtain ⟨h', eq'⟩ := eq _ (le_of_pathIn_right path) step.h₂
  exact ⟨i', cs'', NFA.pathIn.cast start eq path, step.cast h' eq'⟩

theorem NFA.pathToNext.castLE {nfa : NFA} {next start start' i : Nat} {cs cs' : List Char}
  (assm : start' ≤ i)
  (inBounds : ∀ i j, (h₁ : start' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    start ≤ j →
    start' ≤ j)
  (path : NFA.pathToNext nfa next start i cs cs') :
  NFA.pathToNext nfa next start' i cs cs' := by
  obtain ⟨i', cs'', path, step⟩ := path
  have path' := path.castLE assm inBounds
  exact ⟨i', cs'', path', step.castStart' (le_of_pathIn_right path')⟩

theorem eq_next_of_pathToNext (eq : compile.loop r next nfa = result)
  (assm : next' < nfa.nodes.size)
  (path : NFA.pathToNext result next' nfa.nodes.size i cs cs') :
  next' = next := by
  obtain ⟨i', cs'', path, step⟩ := path
  have step_range := compile.loop.step_range eq i' (le_of_pathIn_right path) step.h₂
  have mem : next' ∈ {next} ∪ compile.loop.NewNodesRange eq := by
    cases step with
    | charStep _ _ step => exact Set.mem_of_mem_of_subset step (step_range.left _)
    | εStep _ _ step => exact Set.mem_of_mem_of_subset step step_range.right
  simp [compile.loop.NewNodesRange] at mem
  cases mem with
  | inl eq => exact eq
  | inr mem => exact absurd mem.left (Nat.not_le_of_lt assm)

theorem pathIn_split (eq : compile.loop r next nfa = result)
  (assm₁ : start < nfa.nodes.size) (assm₂ : i' < nfa.nodes.size) (assm₃ : nfa.nodes.size ≤ i)
  (path : NFA.pathIn result start i cs i' cs') :
  ∃ cs'', NFA.pathToNext result next nfa.nodes.size i cs cs'' ∧
    NFA.pathIn result start next cs'' i' cs' := by
  induction path with
  | base _ eqi => exact absurd assm₂ (Nat.not_lt_of_le (eqi ▸ assm₃))
  | @step i j k cs cs' cs'' step rest ih =>
    cases Nat.lt_or_ge j nfa.nodes.size with
    | inl lt =>
      have pathToNext : NFA.pathToNext result j nfa.nodes.size i cs cs' :=
        ⟨i, cs, .base assm₃ rfl rfl, step.castStart' assm₃⟩
      have : j = next := eq_next_of_pathToNext eq lt pathToNext
      rw [this] at pathToNext rest
      exact ⟨cs', pathToNext, rest⟩
    | inr ge =>
      obtain ⟨cs''', pathToNext, pathIn⟩ := ih assm₂ ge
      exact ⟨cs''', pathToNext.cons (step.castStart' assm₃), pathIn⟩

inductive NFA.starLoop (eq : compile.loop (.star r) next nfa = result) : List Char → List Char → Prop where
  | complete (eqs : cs = cs') : starLoop eq cs cs'
  | loop (eqr : result.val[nfa.nodes.size]'(compile.loop.lt_size eq) = .split rStart next)
    (path : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) rStart cs cs'')
    (rest : NFA.starLoop eq cs'' cs') : starLoop eq cs cs'

theorem eqr_of_mem_of_le (eq : compile.loop (.star r) next nfa = result)
  (prem₁ : next < nfa.nodes.size)
  (mem : rStart ∈ (result.val[nfa.nodes.size]'(compile.loop.lt_size eq)).εStep)
  (le : nfa.nodes.size + 1 ≤ rStart) :
  result.val[nfa.nodes.size]'(compile.loop.lt_size eq) = .split rStart next := by
  let ⟨_, _, node⟩ := compile.loop.star.loopStartNode eq
  have : rStart ≠ next := Nat.ne_of_gt (lt_trans prem₁ le)
  simp [node, Node.εStep, this] at mem
  rw [node, mem]

theorem NFA.starLoop.intro' (eq : compile.loop (.star r) next nfa = result)
  (prem₁ : next < nfa.nodes.size) (prem₂ : result.val.inBounds)
  (assm₁ : i < result.val.nodes.size) (assm₂ : loopStart = nfa.nodes.size)
  (ev : pathIn result nfa.nodes.size i cs loopStart cs') :
  if i = nfa.nodes.size then
    (cs = cs') ∨
    (∃ j cs'', j < result.val.nodes.size ∧ j ∈ result.val[i].εStep ∧
    pathToNext result nfa.nodes.size (nfa.nodes.size + 1) j cs cs'' ∧ starLoop eq cs'' cs')
  else
    ∃ cs'', pathToNext result nfa.nodes.size (nfa.nodes.size + 1) i cs cs'' ∧ starLoop eq cs'' cs' := by
  induction ev with
  | base h eqi eqs =>
    subst eqi assm₂
    simp
    exact .inl eqs
  | @step i j k cs cs'' cs' step path ih =>
    have ih := ih (step.lt_of_inBounds prem₂) assm₂
    split
    case inl eqi =>
      subst eqi
      obtain ⟨rStart, range, node⟩ := compile.loop.star.loopStartNode eq
      cases step with
      | charStep _ _ step => simp [node, Node.charStep] at step
      | εStep h₁ h₂ step =>
        have : j = rStart := by
          simp [node, Node.εStep] at step
          cases step with
          | inl eq => exact eq
          | inr eq =>
            have : nfa.nodes.size ≤ j := le_of_pathIn_left path
            exact absurd prem₁ (Nat.not_lt_of_le (eq ▸ this))
        subst this
        simp at range
        have : j ≠ nfa.nodes.size := Nat.ne_of_gt range.left
        simp [this] at ih
        obtain ⟨cs'', path', l⟩ := ih
        exact .inr ⟨j, cs'', lt_of_inBounds_of_εStep prem₂ step, step, path', l⟩
    case inr nei =>
      have gti : nfa.nodes.size < i := Nat.lt_of_le_of_ne step.h₁ (Ne.symm nei)
      split at ih
      case inl eqj =>
        have toNext : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) i cs cs'' :=
          ⟨i, cs, .base gti rfl rfl, (eqj ▸ step).castStart' gti⟩
        cases ih with
        | inl eqs =>
          exists cs''
          exact ⟨toNext, .complete eqs⟩
        | inr cond =>
          obtain ⟨j', cs''', _, h', path', l⟩ := cond
          have : result.val[nfa.nodes.size]'(compile.loop.lt_size eq) = .split j' next :=
            eqr_of_mem_of_le eq prem₁ (eqj ▸ h') (le_of_pathToNext path')
          exact ⟨cs'', toNext, .loop this path' l⟩
      case inr nej =>
        obtain ⟨cs'', path, loop⟩ := ih
        exact ⟨cs'', path.cons (step.castStart' gti), loop⟩

theorem NFA.starLoop.intro (eq : compile.loop (.star r) next nfa = result)
  (prem₁ : next < nfa.nodes.size) (prem₂ : result.val.inBounds)
  (ev : pathIn result nfa.nodes.size nfa.nodes.size cs nfa.nodes.size cs') :
  starLoop eq cs cs' := by
  have : nfa.nodes.size < result.val.nodes.size := compile.loop.lt_size eq
  let loop := starLoop.intro' eq prem₁ prem₂ this rfl ev
  simp at loop
  match loop with
  | .inl eqs => exact .complete eqs
  | .inr ⟨rStart, _, step, ⟨_, path, loop⟩⟩ =>
    have : result.val[nfa.nodes.size]'(compile.loop.lt_size eq) = .split rStart next :=
        eqr_of_mem_of_le eq prem₁ step (le_of_pathToNext path)
    exact .loop this path loop

theorem matches_prefix_of_starLoop (eq : compile.loop (.star r) next nfa = result)
  (mr : ∀ {cs cs'} rStart,
    result.val[Array.size nfa.nodes]'(compile.loop.lt_size eq) = Node.split rStart next →
    NFA.pathToNext result (Array.size nfa.nodes) (Array.size nfa.nodes + 1) rStart cs cs' →
    ∃ p, cs = p ++ cs' ∧ r.matches ⟨p⟩)
  (loop : NFA.starLoop eq cs cs') :
  ∃ p, cs = p ++ cs' ∧ (Regex.star r).matches ⟨p⟩ := by
  induction loop with
  | complete eqs => exact ⟨[], eqs, .starEpsilon rfl⟩
  | loop eqr path _ ih =>
    let ⟨p₁, eqs₁, m₁⟩ := mr _ eqr path
    let ⟨p₂, eqs₂, m₂⟩ := ih
    exact ⟨p₁ ++ p₂, by simp [eqs₁, eqs₂], .starConcat _ _ _ _ rfl m₁ m₂⟩

theorem matches_prefix_of_path (eq : compile.loop r next nfa = result)
  (h₁ : next < nfa.nodes.size) (h₂ : nfa.inBounds)
  (path : NFA.pathToNext result next nfa.nodes.size result.val.start.val s s') :
  ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
  induction r generalizing next nfa s s' with
  | empty =>
    apply compile.loop.empty eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, Node.charStep, Node.εStep] at *
  | epsilon =>
    apply compile.loop.epsilon eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, Node.charStep, Node.εStep] at *
    cases path with
    | base _ _ eqs => exact ⟨[], eqs, .epsilon rfl⟩
    | step step rest =>
      cases step with
      | charStep _ _ step => simp [Node.charStep] at step
      | εStep _ _ step =>
        simp [Node.εStep] at step
        have := le_of_pathIn_left rest
        exact absurd h₁ (Nat.not_lt_of_ge (step ▸ this))
  | char c =>
    apply compile.loop.char eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, Node.charStep, Node.εStep] at *
    next eqc =>
      rw [eqc] at path
      cases path with
      | base _ _ eqs => exact ⟨[c], eqs, .char c rfl⟩
      | step step rest =>
        cases step with
        | charStep _ _ step =>
          simp [Node.charStep] at step
          have := le_of_pathIn_left rest
          exact absurd h₁ (Nat.not_lt_of_ge (step.right ▸ this))
        | εStep _ _ step => simp [Node.εStep] at step
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ eq₃ eq₄ eq₅ eq

    have inBounds₁ := compile.loop.inBounds eq₁.symm h₁ h₂
    have inBounds₂ :=
      compile.loop.inBounds eq₃.symm (Nat.lt_of_lt_of_le h₁ nfa₁.property) inBounds₁
    have size₁ : next < nfa₁.val.nodes.size := Nat.lt_of_lt_of_le h₁ nfa₁.property
    have startNode : final.val[final.val.start.val] = .split start₁ start₂ := by
      rw [eq₅]
      simp

    have le₂ : nfa₂.val.nodes.size ≤ final.val.nodes.size := by
      rw [eq₅]
      simp [NFA.addNode]
      exact Nat.le_of_lt (Nat.lt_succ_self _)
    have le₁ : nfa₁.val.nodes.size ≤ final.val.nodes.size := le_trans nfa₂.property le₂
    have leStart : nfa₁.val.nodes.size ≤ start₂ := by
      rw [eq₄]
      have := compile.loop.start_in_NewNodesRange eq₃.symm
      simp [compile.loop.NewNodesRange] at this
      exact this
    have neStart₁ : next ≠ start₁ := by
      apply Nat.ne_of_lt
      have := compile.loop.start_in_NewNodesRange eq₁.symm
      simp [compile.loop.NewNodesRange] at this
      exact Nat.lt_of_lt_of_le h₁ (eq₂.symm ▸ this)
    have neStart₂ : next ≠ start₂ := by
      intro h
      rw [←h] at leStart
      exact absurd leStart (Nat.not_le_of_gt size₁)

    have get₂ (i : Nat) (h : i < nfa₂.val.nodes.size) :
      nfa₂.val[i] = final.val[i]'(Nat.lt_of_lt_of_le h le₂) := by
      simp [eq₅]
      rw [NFA.get_lt_addNode h]
    have get₁ (i : Nat) (h : i < nfa₁.val.nodes.size) :
      nfa₁.val[i] = final.val[i]'(Nat.lt_of_lt_of_le h le₁) := by
      rw [(get₂ i (Nat.lt_of_lt_of_le h nfa₂.property)).symm]
      rw [compile.loop.get_lt eq₃.symm h]

    have inBounds₁' (i j : Nat) (h : i < nfa₁.val.nodes.size)
      (step : (∃ c, j ∈ nfa₁.val[i].charStep c) ∨ j ∈ nfa₁.val[i].εStep) :
      j < nfa₁.val.nodes.size := by
      match step with
      | .inl ⟨_, step⟩ => exact lt_of_inBounds_of_charStep inBounds₁ step
      | .inr step => exact lt_of_inBounds_of_εStep inBounds₁ step
    have inBounds₂' (i j : Nat) (h : i < nfa₂.val.nodes.size)
      (step : (∃ c, j ∈ nfa₂.val[i].charStep c) ∨ j ∈ nfa₂.val[i].εStep) :
      j < nfa₂.val.nodes.size := by
      match step with
      | .inl ⟨_, step⟩ => exact lt_of_inBounds_of_charStep inBounds₂ step
      | .inr step => exact lt_of_inBounds_of_εStep inBounds₂ step

    have step_range₂_ge (i j : Nat) (h₁ : nfa₁.val.nodes.size ≤ i) (h₂ : i < nfa₂.val.nodes.size)
      (step : (∃ c, j ∈ nfa₂.val[i].charStep c) ∨ j ∈ nfa₂.val[i].εStep)
      (le : nfa.nodes.size ≤ j):
      nfa₁.val.nodes.size ≤ j := by
      have step_range := compile.loop.step_range eq₃.symm i h₁ h₂
      simp [compile.loop.NewNodesRange] at step_range
      match step with
      | .inl ⟨c, step⟩ =>
        have range := Set.mem_of_mem_of_subset step (step_range.left c)
        simp at range
        cases range with
        | inl eq =>
          rw [eq] at le
          exact absurd le (Nat.not_le_of_gt ‹next < nfa.nodes.size›)
        | inr range => exact range.left
      | .inr step =>
        have range := Set.mem_of_mem_of_subset step step_range.right
        simp at range
        cases range with
        | inl eq =>
          rw [eq] at le
          exact absurd le (Nat.not_le_of_gt ‹next < nfa.nodes.size›)
        | inr range => exact range.left

    rw [eq] at path
    simp at path

    obtain ⟨i', s'', path, step⟩ := path
    cases path with
    | base _ eqi =>
      rw [←eqi] at step
      cases step with
      | charStep _ _ step => simp [startNode, Node.charStep] at step
      | εStep _ _ step =>
        simp [startNode, Node.εStep] at step
        cases step <;> contradiction
    | step step' rest =>
      cases step' with
      | charStep _ _ step' => simp [startNode, Node.charStep] at step'
      | εStep _ _ step' =>
        simp [startNode, Node.εStep] at step'
        cases step' with
        | inl step₁ =>
          subst step₁
          have path₁ := rest.cast' (nfa := nfa₁) start₁.isLt le₁ (fun i _ => get₁ i) inBounds₁'
          have h' : i' < nfa₁.val.nodes.size := path₁.lt_of_lt start₁.isLt inBounds₁'
          have path₁ : NFA.pathToNext nfa₁ next nfa.nodes.size nfa₁.val.start s s' :=
            ⟨i', s'', eq₂ ▸ path₁, step.cast h' (get₁ i' h').symm⟩
          let ⟨p, eqs, m₁⟩ := ih₁ eq₁.symm h₁ h₂ path₁
          exact ⟨p, eqs, .alternateLeft m₁⟩
        | inr step₂ =>
          subst step₂
          have path₂ := rest.cast' (nfa := nfa₂) start₂.isLt le₂ (fun i _ => get₂ i) inBounds₂'
          have path₂ := path₂.castLE leStart step_range₂_ge
          have h' : i' < nfa₂.val.nodes.size := path₂.lt_of_lt start₂.isLt inBounds₂'
          have path₂ : NFA.pathToNext nfa₂ next nfa₁.val.nodes.size nfa₂.val.start s s' :=
            ⟨i', s'', eq₄ ▸ path₂, (step.cast h' (get₂ i' h').symm).castStart' (le_of_pathIn_right path₂)⟩
          let ⟨p, eqs, m₂⟩ := ih₂ eq₃.symm size₁ inBounds₁ path₂
          exact ⟨p, eqs, .alternateRight m₂⟩
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    have inBounds₂ := compile.loop.inBounds eq₂.symm h₁ h₂
    have inBounds₁ := compile.loop.inBounds eq₁.symm nfa₂.val.start.isLt inBounds₂

    have lt_size : nfa.nodes.size < nfa₂.val.nodes.size := compile.loop.lt_size eq₂.symm
    have le_start₁ : nfa₂.val.nodes.size ≤ nfa₁.val.start := by
      have := compile.loop.start_in_NewNodesRange eq₁.symm
      simp [compile.loop.NewNodesRange] at this
      exact this
    have ne : next ≠ nfa₂.val.start := by
      apply Nat.ne_of_lt
      have := compile.loop.start_in_NewNodesRange eq₂.symm
      simp [compile.loop.NewNodesRange] at this
      exact Nat.lt_of_lt_of_le h₁ this
    have not_le : ¬ nfa₂.val.nodes.size ≤ next := by
      apply Nat.not_le_of_gt
      exact lt_trans h₁ lt_size
    have cast_path₂ {cs cs'} (i' : Nat) (_ : i' < nfa₂.val.nodes.size)
      (path : NFA.pathIn nfa₁ nfa.nodes.size nfa₂.val.start cs i' cs') :
      NFA.pathIn nfa₂ nfa.nodes.size nfa₂.val.start cs i' cs' := by
      refine NFA.pathIn.cast' nfa₂.val.start.isLt nfa₁.property ?eq ?inBounds path
      case eq =>
        intro i _ h₂
        rw [compile.loop.get_lt eq₁.symm]
      case inBounds =>
        intro i j h step
        match step with
        | .inl ⟨_, step⟩ => exact lt_of_inBounds_of_charStep inBounds₂ step
        | .inr step => exact lt_of_inBounds_of_εStep inBounds₂ step

    rw [eq] at path
    simp at path

    obtain ⟨i', s''', path, step⟩ := path
    have lt : i' < nfa₁.val.nodes.size := step.h₂
    have h' : i' < nfa₂.val.nodes.size := by
      cases Nat.lt_or_ge i' nfa₂.val.nodes.size with
      | inl lt => exact lt
      | inr ge =>
        have step_range := compile.loop.step_range eq₁.symm i' ge lt
        cases step with
        | charStep _ _ step =>
          have mem := Set.mem_of_mem_of_subset step (step_range.left _)
          simp [compile.loop.NewNodesRange, ne, not_le] at mem
        | εStep _ _ step =>
          have mem := Set.mem_of_mem_of_subset step step_range.right
          simp [compile.loop.NewNodesRange, ne, not_le] at mem
    have eq : nfa₁.val[i'] = nfa₂.val[i'] := by rw [compile.loop.get_lt eq₁.symm]
    let ⟨s'', path₁, path₂⟩ := pathIn_split eq₁.symm lt_size h' le_start₁ path
    have path₂ := cast_path₂ i' h' path₂
    have path₂ : NFA.pathToNext nfa₂ next (Array.size nfa.nodes) nfa₂.val.start s'' s' :=
      ⟨i', s''', path₂, step.cast h' eq⟩
    let ⟨p₁, eqs₁, m₁⟩ := ih₁ eq₁.symm nfa₂.val.start.isLt inBounds₂ path₁
    let ⟨p₂, eqs₂, m₂⟩ := ih₂ eq₂.symm h₁ h₂ path₂
    exact ⟨p₁ ++ p₂, by simp [eqs₁, eqs₂], .concat _ _ _ _ _ rfl m₁ m₂⟩
  | star r ih =>
    apply compile.loop.star eq
    intro placeholder loopStart compiled nodes patched isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq'

    have placeholder.inBounds : placeholder.val.inBounds := by
      intro i
      cases Nat.lt_or_ge i nfa.nodes.size with
      | inl lt =>
        have : placeholder.val[i] = nfa[i] := by
          simp [eq₁, NFA.get_lt_addNode lt]
        rw [this]
        exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) placeholder.property
      | inr ge =>
        have : i < nfa.nodes.size + 1 := by
          have : i < placeholder.val.nodes.size := i.isLt
          simp [eq₁, NFA.addNode] at this
          exact this
        have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge this
        have : placeholder.val[i] = .fail := by
          simp [eq₁, this]
        rw [this]
        simp
    have inBounds' : result.val.inBounds := compile.loop.inBounds eq h₁ h₂
    have eql : loopStart.val = nfa.nodes.size := by
      simp [eq₂]
      rw [eq₁]
      simp [NFA.addNode]
    have eqStart : result.val.start.val = nfa.nodes.size := by
      rw [eq']
      simp
      rw [eq₅]
      simp [eql]
    rw [eqStart] at path

    have eqSize : result.val.nodes.size = compiled.val.nodes.size := by
      simp [eq', eq₅, eq₄]
    have firstNode : result.val[nfa.nodes.size]'(compile.loop.lt_size eq) = .split compiled.val.start next := by
      simp [eq']
      simp [eq₅, NFA.eq_get, eq₄, eql.symm]
    have compiledNodes (i : Nat) (h₁ : nfa.nodes.size < i) (h₂ : i < result.val.nodes.size) :
      result.val[i] = compiled.val[i]'(eqSize ▸ h₂) := by
      simp [eq', eq₅, NFA.eq_get, eq₄]
      have : (Fin.mk loopStart.val isLt).val ≠ i := by
        rw [eql]
        exact Nat.ne_of_lt h₁
      apply Array.get_set_ne _ _ _ _ this
    have compiledNodesRange (i : Nat) (h₁ : nfa.nodes.size < i) (h₂ : i < result.val.nodes.size) :
      (∀ c, next ∉ result.val[i].charStep c) ∧ next ∉ result.val[i].εStep := by
      rw [compiledNodes i h₁ h₂]
      have : nfa.nodes.size + 1 = placeholder.val.nodes.size := by simp [eq₁, NFA.addNode]
      have range := compile.loop.step_range eq₃.symm i (this ▸ h₁) (eqSize ▸ h₂)
      have : next ∉ {loopStart.val} ∪ compile.loop.NewNodesRange eq₃.symm := by
        simp [eql, compile.loop.NewNodesRange]
        intro h
        match h with
        | .inl eq => exact absurd eq (Nat.ne_of_lt ‹next < nfa.nodes.size›)
        | .inr ⟨h₁', _⟩ =>
          simp [eq₁, NFA.addNode] at h₁'
          exact absurd (le_trans (Nat.le_succ _) h₁') (Nat.not_le_of_lt ‹next < nfa.nodes.size›)
      exact ⟨
        fun c h => this (Set.mem_of_mem_of_subset h (range.left c)),
        fun h => this (Set.mem_of_mem_of_subset h range.right)
      ⟩

    -- Within the range of the nodes for `r`, we can use the induction hypothesis
    -- by casting the path from `result` to `compiled`.
    have mr {cs cs' : List Char}
      (rStart : Nat)
      (eqr : result.val[Array.size nfa.nodes]'(compile.loop.lt_size eq) = Node.split rStart next)
      (path : NFA.pathToNext result (Array.size nfa.nodes) (Array.size nfa.nodes + 1) rStart cs cs') :
      ∃ p, cs = p ++ cs' ∧ r.matches ⟨p⟩ := by
      simp [firstNode] at eqr
      rw [←eqr] at path
      have : NFA.pathToNext compiled loopStart placeholder.val.nodes.size compiled.val.start cs cs' := by
        simp [eq₁, NFA.addNode]
        simp [eql]
        apply path.cast
        intro i h₁ h₂
        rw [eq'] at h₂
        simp [eq₅, eq₄] at h₂
        exists h₂
        have ne : (Fin.mk loopStart.val isLt).val ≠ i := by
          simp [eql]
          exact Nat.ne_of_lt h₁
        conv =>
          lhs
          simp [eq', eq₅, NFA.eq_get, eq₄, Array.get_set_ne _ _ _ h₂ ne]
      exact ih (s := cs) (s' := cs') eq₃.symm loopStart.isLt placeholder.inBounds this

    obtain ⟨i', cs'', path, step⟩ := path
    have lt' : i' < result.val.nodes.size := step.h₂
    cases step with
    | charStep _ _ step =>
      -- No nodes can perform charStep to `next`.
      cases Nat.eq_or_lt_of_le (le_of_pathIn_right path) with
      | inl eq => simp [eq.symm, firstNode, Node.charStep] at step
      | inr lt => exact absurd step ((compiledNodesRange i' lt lt').left _)
    | εStep _ _ step =>
      -- Only the loop start can perform εStep to `next`.
      have : i' = nfa.nodes.size := by
        cases Nat.eq_or_lt_of_le (le_of_pathIn_right path) with
        | inl eq => exact eq.symm
        | inr lt => exact absurd step (compiledNodesRange i' lt lt').right
      subst this
      have loop := NFA.starLoop.intro eq h₁ inBounds' path
      exact matches_prefix_of_starLoop eq mr loop

theorem matches_prefix_of_path' (eq : compile r = nfa)
  (path : nfa.pathToNext 0 1 nfa.start.val s s') :
  ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
  generalize eq' : compile.loop r 0 compile.init = result
  have : nfa = result.val := by
    simp [eq.symm, compile, eq'.symm]
  exact matches_prefix_of_path eq' (by decide) compile.init.inBounds (this ▸ path)

theorem matches_of_path (eq : compile r = nfa) (path : nfa.pathToNext 0 1 nfa.start.val s []) :
  r.matches ⟨s⟩ := by
  let ⟨_, eqs, m⟩ := matches_prefix_of_path' eq path
  simp [eqs]
  exact m

end NFA
