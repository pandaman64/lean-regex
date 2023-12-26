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

theorem εClosure_subset_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) :
  nfa₁.εClosure i ⊆ nfa₂.εClosure i := by
  intro j h
  exact εClosure_of_le le h

theorem εClosure_trans {nfa : NFA} (h₁ : i₂ ∈ nfa.εClosure i₁) (h₂ : i₃ ∈ nfa.εClosure i₂) :
  i₃ ∈ nfa.εClosure i₁ := by
  induction h₁ with
  | base => exact h₂
  | step head _ ih => exact .step head (ih h₂)

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

theorem mem_evalFrom_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : next ∈ nfa₁.evalFrom S s) :
  next ∈ nfa₂.evalFrom S s :=
  evalFrom_subset le (le_refl _) h

open NFA

theorem evalFrom_of_matches (eq : compile.loop r next nfa = nfa')
  (m : r.matches s) : ∀ nfa'' : NFA, nfa' ≤ nfa'' → next ∈ nfa''.evalFrom {nfa'.val.start.val} s.data := by
  induction m generalizing next nfa with
  | @char s c eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, List.foldl]
    simp [compile.loop] at eq
    apply mem_iUnion_of_mem nfa'.val.start.val
    subst eq
    simp [Option.charStep, Node.charStep]
  | @epsilon s eqs =>
    intro nfa'' le
    apply mem_evalFrom_le le
    simp [eqs, evalFrom, List.foldl]
    simp [compile.loop] at eq
    apply mem_iUnion_of_mem nfa'.val.start.val
    subst eq
    simp [Option.charStep, Node.charStep]
    exact εClosure.step (by simp [Option.εStep, Node.εStep]) .base
  | @alternateLeft s r₁ r₂ _ ih =>
    intro nfa'' le
    apply mem_evalFrom_le le

    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ _ _ eq₅ eq

    have property : nfa₁.val ≤ final.val :=
      calc nfa₁.val
        _ ≤ nfa₂.val := nfa₂.property
        _ ≤ final.val := final.property

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

    apply mem_evalFrom_subset (ih eq₃.symm final final.property)
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
    let ih₂ := ih₂ eq₂.symm nfa₁ nfa₁.property

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
            rw [eq₂, eq₁]
            simp
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

-- こんな感じのが必要では
-- def NFA.evalFromUntil (nfa : NFA) (S : Set Nat) (next : Nat) (s : List Char) : Option (List Char) :=
--   if next ∈ S then
--     some s
--   else
--     match s with
--     | [] => none
--     | c :: s => nfa.evalFromUntil (nfa.stepSet S c) next s

def NFA.stepSet' (nfa : NFA) (S : Set Nat) (c : Char) : Set Nat :=
  ⋃ i ∈ nfa.εClosureSet S, nfa.εClosureSet (nfa[i]?.charStep c)

theorem compile.loop.εClosure_subset (eq : compile.loop r next nfa = result)
  (h : i ∈ NewNodesRange eq) (cls : j ∈ result.val.εClosure i) :
  j ∈ result.val.εClosure next ∪ NewNodesRange eq := by
  induction cls with
  | base => exact Or.inr h
  | @step i j k head tail ih =>
    simp [Option.εStep.simp, h.right] at head
    -- Use whatever char
    let ⟨_, h⟩ := step_range (c := default) eq i h.left h.right
    have : j = next ∨ j ∈ NewNodesRange eq := mem_insert_iff.mp (mem_of_mem_of_subset head h)
    cases this with
    | inl h => exact mem_union_left _ (h ▸ tail)
    | inr h => exact ih h

theorem compile.loop.εClosureSet_NewNodesRange (eq : compile.loop r next nfa = result) :
  result.val.εClosureSet (NewNodesRange eq) ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
  simp [NFA.εClosureSet]
  intro i h
  simp [subset_def]
  intro j cls
  exact εClosure_subset eq h cls

theorem compile.loop.εClosureSet_subset (eq : compile.loop r next nfa = result)
  (h : S ⊆ {next} ∪ NewNodesRange eq) :
  result.val.εClosureSet S ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
  calc result.val.εClosureSet S
    _ ⊆ result.val.εClosureSet ({next} ∪ NewNodesRange eq) := by
      apply NFA.εClosureSet_subset
      . exact le_refl _
      . exact h
    _ = result.val.εClosureSet {next} ∪ result.val.εClosureSet (NewNodesRange eq) :=
      εClosureSet_union_distrib
    _ ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
      simp [εClosureSet_NewNodesRange]
      simp [εClosureSet]

theorem compile.loop.stepSet_subset (eq : compile.loop r next nfa = result)
  (h : S ⊆ NewNodesRange eq) :
  result.val.stepSet S c ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
  simp [NFA.stepSet]
  intro i h'
  have : i ∈ NewNodesRange eq := mem_of_subset_of_mem h h'
  have h'' : nfa.nodes.size ≤ i ∧ i < result.val.nodes.size := by
    simp [NewNodesRange] at this
    exact this
  apply εClosureSet_subset eq
  simp [Option.charStep.simp, h''.right]
  let ⟨h, _⟩ := step_range c eq i h''.left h''.right
  exact h

inductive NFA.eval (nfa : NFA) : Set Nat → List Char → Set Nat → List Char → Prop where
  | base : nfa.eval S cs S cs
  | step (rest : nfa.eval (nfa.stepSet' S c) cs S' cs') : nfa.eval S (c :: cs) S' cs'

theorem NFA.eval_prefix {nfa : NFA} (ev : nfa.eval S s S' s₂) :
  ∃s₁, s = s₁ ++ s₂ := by
  induction ev with
  | base => exists []
  | @step _ c _ _ _ _ ih =>
    let ⟨s₁', h⟩ := ih
    exists c :: s₁'
    simp [h]

notation:65 nfa " ⊢ (" S ", " s ") ⟶* (" S' ", " s' ")" => NFA.eval nfa S s S' s'

theorem eval_to_next_of_eval (eq : compile.loop r next nfa = result)
  -- hsはnextを含むのかな？含まない気もしてきた
  -- そもそもstartが{result.val.start}にした方がいいのかも
  (ev : result ⊢ (S, s) ⟶* (S', s')) (hs : S ⊆ {next} ∪ compile.loop.NewNodesRange eq)
  (h₁ : i ∈ S') (h₂ : i < nfa.nodes.size) :
  ∃ S'' s'', result ⊢ (S, s) ⟶* (S'', s'') ∧ next ∈ S'' := by
  induction ev with
  | @base S cs =>
    exists S, cs, .base
    have : i ∈ {next} ∪ compile.loop.NewNodesRange eq :=
      mem_of_subset_of_mem hs h₁
    have : i = next ∨ i ∈ compile.loop.NewNodesRange eq :=
      mem_insert_iff.mp this
    cases this with
    | inl h => exact h ▸ h₁
    | inr h =>
      simp [compile.loop.NewNodesRange] at h
      exact (Nat.not_lt_of_ge h.left h₂).elim
  | @step S c cs S' cs' rest ih => sorry

theorem matches_of_eval (eq : compile.loop r next nfa = nfa') (assm : next < nfa.nodes.size)
  (ev : nfa' ⊢ ({nfa'.val.start.val}, s) ⟶* (S', s')) (h : next ∈ S') : ∃p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
  induction r generalizing next nfa s S' s' with
  | empty =>
    apply compile.loop.empty eq
    intro eq

    sorry
  | epsilon => sorry
  | char c => sorry
  | alternate r₁ r₂ => sorry
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    -- ここでS₁はnfa₂.val.start.valを含むような奴が実はとれる
    have ev₁ : ∃S₁ s₂_s', nfa₁ ⊢ ({nfa₁.val.start.val}, s) ⟶* (S₁, s₂_s') := sorry
    let ⟨S₁, s₂_s', ev₁⟩ := ev₁
    have h₁ : nfa₂.val.start.val ∈ S₁ := sorry
    have ⟨s₁, eqs₁, m₁⟩ := ih₁ eq₁.symm nfa₂.val.start.isLt ev₁ h₁

    have ev₂ : nfa₂ ⊢ ({nfa₂.val.start.val}, s₂_s') ⟶* (S', s') := sorry
    have h₂ : next ∈ S' := sorry
    have ⟨s₂, eqs₂, m₂⟩ := ih₂ eq₂.symm assm ev₂ h₂

    have eqs : s = s₁ ++ s₂ ++ s' := by
      rw [List.append_assoc]
      exact eqs₂ ▸ eqs₁

    exact ⟨s₁ ++ s₂, eqs, .concat ⟨s₁ ++ s₂⟩ ⟨s₁⟩ ⟨s₂⟩ r₁ r₂ rfl m₁ m₂⟩
  | star r => sorry

end NFA
