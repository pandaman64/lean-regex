import Regex.Lemmas
import Regex.NFA.Basic
import Regex.NFA.Compile

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Lattice

open Set

-- TODO: we may want to prove that all indices are in bounds get rid of Option helpers.
-- def Option.charStep : Option NFA.Node → Char → Set Nat
--   | some n, c => n.charStep c
--   | none, _ => ∅

-- def Option.εStep : Option NFA.Node → Set Nat
--   | some n => n.εStep
--   | none => ∅

namespace NFA

-- def Option.charStep.simp {nfa : NFA} {i : Nat} {c : Char} :
--   nfa[i]?.charStep c = if h : i < nfa.nodes.size then nfa[i].charStep c else ∅ := by
--   simp [Option.charStep, getElem?]
--   cases Nat.decLt i nfa.nodes.size <;> simp [*]

-- theorem Option.charStep.subset_of_le {nfa₁ nfa₂ : NFA} {i : Nat} (le : nfa₁ ≤ nfa₂) :
--   nfa₁[i]?.charStep c ⊆ nfa₂[i]?.charStep c := by
--   simp [Option.charStep.simp]
--   cases Nat.decLt i nfa₁.nodes.size <;> simp [*]
--   case isTrue h =>
--     let ⟨h', le⟩ := le i h
--     simp [h']
--     exact le.left c

-- def Option.εStep.simp {nfa : NFA} {i : Nat} :
--   nfa[i]?.εStep = if h : i < nfa.nodes.size then nfa[i].εStep else ∅ := by
--   simp [Option.εStep, getElem?]
--   cases Nat.decLt i nfa.nodes.size <;> simp [*]

-- theorem Option.εStep.subset_of_le {nfa₁ nfa₂ : NFA} {i : Nat} (le : nfa₁ ≤ nfa₂) :
--   nfa₁[i]?.εStep ⊆ nfa₂[i]?.εStep := by
--   simp [Option.εStep.simp]
--   cases Nat.decLt i nfa₁.nodes.size <;> simp [*]
--   case isTrue h =>
--     let ⟨h', le⟩ := le i h
--     simp [h']
--     exact le.right

-- inductive NFA.εClosure (nfa : NFA) : Nat → Set Nat where
--   | base : εClosure nfa i i
--   | step {i j k : Nat} (head : j ∈ nfa[i]?.εStep) (tail : nfa.εClosure j k) :
--     εClosure nfa i k

-- theorem εClosure_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : j ∈ nfa₁.εClosure i) :
--   j ∈ nfa₂.εClosure i := by
--   induction h with
--   | base => exact .base
--   | step head _ ih => exact .step (mem_of_subset_of_mem (Option.εStep.subset_of_le le) head) ih

-- theorem εClosure_subset_of_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) :
--   nfa₁.εClosure i ⊆ nfa₂.εClosure i := by
--   intro j h
--   exact εClosure_of_le le h

-- theorem εClosure_trans {nfa : NFA} (h₁ : i₂ ∈ nfa.εClosure i₁) (h₂ : i₃ ∈ nfa.εClosure i₂) :
--   i₃ ∈ nfa.εClosure i₁ := by
--   induction h₁ with
--   | base => exact h₂
--   | step head _ ih => exact .step head (ih h₂)

-- def NFA.εClosureSet (nfa : NFA) (S : Set Nat) : Set Nat :=
--   ⋃ i ∈ S, nfa.εClosure i

-- @[simp]
-- theorem subset_εClosureSet {nfa : NFA} : S ⊆ nfa.εClosureSet S := by
--   intro i h
--   apply mem_iUnion_of_mem i
--   simp
--   exact ⟨h, .base⟩

-- @[simp]
-- theorem εClosureSet_singleton_base {nfa : NFA} : i ∈ nfa.εClosureSet {i} := by
--   apply mem_iUnion_of_mem i
--   simp
--   exact .base

-- @[simp]
-- theorem εClosureSet_singleton_step {nfa : NFA} {i j : Nat} (h : j ∈ nfa[i]?.εStep) : j ∈ nfa.εClosureSet {i} := by
--   apply mem_iUnion_of_mem i
--   simp
--   exact .step h .base

-- @[simp]
-- theorem εClosureSet_singleton {nfa : NFA} {i j : Nat} (h : j ∈ nfa.εClosure i):
--   j ∈ nfa.εClosureSet {i} := by
--   apply mem_iUnion_of_mem i
--   simp [h]

-- @[simp]
-- theorem εClosureSet_empty {nfa : NFA} : nfa.εClosureSet ∅ = ∅ := by
--   simp [NFA.εClosureSet]

-- @[simp]
-- theorem εClosureSet_univ {nfa : NFA} : nfa.εClosureSet univ = univ :=
--   univ_subset_iff.mp subset_εClosureSet

-- theorem εClosureSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
--   nfa₁.εClosureSet S₁ ⊆ nfa₂.εClosureSet S₂ := by
--   apply biUnion_mono hs
--   intro i _
--   exact εClosure_subset_of_le hn

-- @[simp]
-- theorem εClosureSet_idempotent {nfa : NFA} : nfa.εClosureSet (nfa.εClosureSet S) = nfa.εClosureSet S := by
--   apply eq_of_subset_of_subset
--   . simp [subset_def]
--     intro k h
--     simp [mem_iUnion, NFA.εClosureSet] at h
--     let ⟨i, h, j, cls, cls'⟩ := h
--     exact mem_iUnion_of_mem i (mem_iUnion_of_mem h (εClosure_trans cls cls'))
--   . apply subset_εClosureSet

-- theorem εClosureSet_iUnion_distrib {nfa : NFA} {S : Set α} {f : α → Set Nat} :
--   nfa.εClosureSet (⋃ i ∈ S, f i) = ⋃ i ∈ S, nfa.εClosureSet (f i) := by
--   simp [NFA.εClosureSet]

-- theorem εClosureSet_union_distrib {nfa : NFA} {S₁ S₂ : Set Nat} :
--   nfa.εClosureSet (S₁ ∪ S₂) = nfa.εClosureSet S₁ ∪ nfa.εClosureSet S₂ := by
--   apply eq_of_subset_of_subset
--   . simp [subset_def]
--     intro j h
--     simp [NFA.εClosureSet] at *
--     let ⟨i, h, cls⟩ := h
--     cases h with
--     | inl h => exact .inl ⟨i, h, cls⟩
--     | inr h => exact .inr ⟨i, h, cls⟩
--   . simp [subset_def]
--     intro j h
--     simp [NFA.εClosureSet] at *
--     cases h with
--     | inl h =>
--       let ⟨i, h, cls⟩ := h
--       exact ⟨i, .inl h, cls⟩
--     | inr h =>
--       let ⟨i, h, cls⟩ := h
--       exact ⟨i, .inr h, cls⟩

-- def NFA.stepSet (nfa : NFA) (S : Set Nat) (c : Char) : Set Nat :=
--   ⋃ i ∈ S, nfa.εClosureSet (nfa[i]?.charStep c)

-- @[simp]
-- def stepSet_empty {nfa : NFA} : nfa.stepSet ∅ c = ∅ := by
--   simp [NFA.stepSet]

-- @[simp]
-- theorem εClosureSet_stepSet {nfa : NFA} :
--   nfa.εClosureSet (nfa.stepSet S c) = nfa.stepSet S c := by
--   apply eq_of_subset_of_subset
--   . conv =>
--       lhs
--       simp [NFA.stepSet, εClosureSet_iUnion_distrib]
--   . exact subset_εClosureSet

-- theorem stepSet_subset {nfa₁ nfa₂ : NFA} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
--   nfa₁.stepSet S₁ c ⊆ nfa₂.stepSet S₂ c := by
--   simp [subset_def, NFA.stepSet]
--   intro j i h₁ h₂

--   exact ⟨
--     i,
--     mem_of_subset_of_mem hs h₁,
--     mem_of_subset_of_mem (εClosureSet_subset hn (Option.charStep.subset_of_le hn)) h₂
--   ⟩

-- def NFA.evalFrom (nfa : NFA) (S : Set Nat) : List Char → Set Nat :=
--   List.foldl (nfa.stepSet) (nfa.εClosureSet S)

-- theorem evalFrom_cons {nfa : NFA} :
--   nfa.evalFrom S (c :: cs) = nfa.evalFrom (nfa.stepSet (nfa.εClosureSet S) c) cs := by
--   have h : nfa.stepSet (nfa.εClosureSet S) c = nfa.εClosureSet (nfa.stepSet (nfa.εClosureSet S) c) :=
--     εClosureSet_stepSet.symm
--   conv =>
--     lhs
--     simp [NFA.evalFrom]
--     rw [h]

-- theorem evalFrom_subset {nfa₁ nfa₂ : NFA} {S₁ S₂ : Set Nat} (hn : nfa₁ ≤ nfa₂) (hs : S₁ ⊆ S₂) :
--   nfa₁.evalFrom S₁ s ⊆ nfa₂.evalFrom S₂ s := by
--   apply le_foldl_of_le
--   . intro _ _ _ hs
--     exact stepSet_subset hn hs
--   . exact εClosureSet_subset hn hs

-- theorem εClosureSet_evalFrom {nfa : NFA} :
--   nfa.εClosureSet (nfa.evalFrom S s) = nfa.evalFrom S s := by
--   apply eq_of_subset_of_subset
--   . induction s generalizing S with
--     | nil => simp [NFA.evalFrom]; exact le_refl _
--     | cons c cs ih =>
--       rw [evalFrom_cons]
--       exact ih
--   . exact subset_εClosureSet

-- theorem mem_evalFrom_subset {nfa : NFA} (hmem : next ∈ nfa.evalFrom S₁ s) (hs : S₁ ⊆ nfa.εClosureSet S₂) :
--   next ∈ nfa.evalFrom S₂ s := by
--   apply mem_of_subset_of_mem _ hmem
--   apply le_foldl_of_le
--   . intro _ _ _ hs
--     exact stepSet_subset (le_refl _) hs
--   . suffices nfa.εClosureSet S₁ ⊆ nfa.εClosureSet (nfa.εClosureSet S₂) by
--       simp at this
--       exact this
--     exact εClosureSet_subset (le_refl _) hs

-- theorem evalFrom_append {nfa : NFA} (eq : s = s₁ ++ s₂) :
--   nfa.evalFrom S s = List.foldl (nfa.stepSet) (nfa.evalFrom S s₁) s₂ := by
--   conv =>
--     lhs
--     rw [eq, NFA.evalFrom, List.foldl_append]

-- theorem mem_evalFrom_le {nfa₁ nfa₂ : NFA} (le : nfa₁ ≤ nfa₂) (h : next ∈ nfa₁.evalFrom S s) :
--   next ∈ nfa₂.evalFrom S s :=
--   evalFrom_subset le (le_refl _) h

-- open NFA

-- theorem evalFrom_of_matches (eq : compile.loop r next nfa = nfa')
--   (m : r.matches s) : ∀ nfa'' : NFA, nfa' ≤ nfa'' → next ∈ nfa''.evalFrom {nfa'.val.start.val} s.data := by
--   induction m generalizing next nfa with
--   | @char s c eqs =>
--     intro nfa'' le
--     apply mem_evalFrom_le le
--     simp [eqs, evalFrom, List.foldl]
--     simp [compile.loop] at eq
--     apply mem_iUnion_of_mem nfa'.val.start.val
--     subst eq
--     simp [Option.charStep, Node.charStep]
--   | @epsilon s eqs =>
--     intro nfa'' le
--     apply mem_evalFrom_le le
--     simp [eqs, evalFrom, List.foldl]
--     simp [compile.loop] at eq
--     apply mem_iUnion_of_mem nfa'.val.start.val
--     subst eq
--     simp [Option.charStep, Node.charStep]
--     exact εClosure.step (by simp [Option.εStep, Node.εStep]) .base
--   | @alternateLeft s r₁ r₂ _ ih =>
--     intro nfa'' le
--     apply mem_evalFrom_le le

--     apply compile.loop.alternate eq
--     intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ _ _ eq₅ eq

--     have property : nfa₁.val ≤ final.val :=
--       calc nfa₁.val
--         _ ≤ nfa₂.val := nfa₂.property
--         _ ≤ final.val := final.property

--     rw [eq]
--     simp

--     apply mem_evalFrom_subset (ih eq₁.symm final property)
--     simp
--     apply εClosureSet_singleton_step
--     rw [eq₅]
--     simp [Option.εStep, Node.εStep]
--     exact .inl (by rw [eq₂])
--   | @alternateRight s r₁ r₂ _ ih =>
--     intro nfa'' le
--     apply mem_evalFrom_le le

--     apply compile.loop.alternate eq
--     intro nfa₁ start₁ nfa₂ start₂ final property _ _ eq₃ eq₄ eq₅ eq

--     rw [eq]
--     simp

--     apply mem_evalFrom_subset (ih eq₃.symm final final.property)
--     simp
--     apply εClosureSet_singleton_step
--     rw [eq₅]
--     simp [Option.εStep, Node.εStep]
--     exact .inr (by rw [eq₄])
--   | concat s s₁ s₂ r₁ r₂ eqs _ _ ih₁ ih₂ =>
--     intro nfa'' le
--     apply mem_evalFrom_le le

--     apply compile.loop.concat eq
--     intro nfa₂ nfa₁ property eq₂ eq₁ eq

--     rw [eq]
--     simp

--     let ih₁ := ih₁ eq₁.symm nfa₁ (le_refl _)
--     let ih₂ := ih₂ eq₂.symm nfa₁ nfa₁.property

--     apply mem_of_mem_of_subset ih₂
--     rw [evalFrom_append (String.eq_of_append_of_eq_of_append eqs)]
--     apply le_foldl_of_le
--     . intro _ _ _ hs
--       exact stepSet_subset (le_refl _) hs
--     . have : {nfa₂.val.start.val} ⊆ nfa₁.val.evalFrom {nfa₁.val.start.val} s₁.data := by
--         rw [singleton_subset_iff]
--         exact ih₁
--       have : nfa₁.val.εClosureSet {nfa₂.val.start.val} ⊆ nfa₁.val.εClosureSet (nfa₁.val.evalFrom {nfa₁.val.start.val} s₁.data) :=
--         εClosureSet_subset (le_refl _) this
--       rw [εClosureSet_evalFrom] at this
--       exact this
--   | starEpsilon eqs =>
--     intro nfa'' le
--     apply mem_evalFrom_le le

--     apply compile.loop.star eq
--     intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
--       _ _ _ eq₄ eq₅ eq'

--     rw [eq']
--     simp

--     simp [eqs, NFA.evalFrom, NFA.εClosureSet]

--     have : nfa'''[nfa'''.start.val] = .split nfa''.val.start next := by
--       rw [eq₅, NFA.eq_get]
--       simp [eq₄]
--     have head : next ∈ nfa'''[nfa'''.start]?.εStep := by
--       unfold getElem?
--       simp [this, Option.εStep, Node.εStep]
--     have tail : next ∈ nfa'''.εClosure next := .base
--     exact NFA.εClosure.step head tail
--   | starConcat s s₁ s₂ r eqs _ _ ih₁ ih₂ =>
--     intro nfa'' le
--     apply mem_evalFrom_le le

--     apply compile.loop.star eq
--     intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
--       eq₁ eq₂ eq₃ eq₄ eq₅ eq'

--     rw [eq']
--     simp

--     have eq'' : compile.loop (.star r) next nfa = ⟨nfa''', property'⟩ := by
--       rw [eq'] at eq
--       exact eq
--     have : nfa''.val ≤ nfa''' := by
--       intro i h
--       have : nodes'''.size = nfa''.val.nodes.size := by
--         simp [eq₄]
--       have : i < nodes'''.size := by
--         simp [this, h]
--       have h' : i < nfa'''.nodes.size := by
--         simp [eq₅, this]
--       exists h'
--       cases Nat.decEq start i with
--       | isTrue eq =>
--         have lhs : nfa''.val[i] = .fail := by
--           simp [eq₃, eq.symm]
--           have : start.val < nfa'.val.nodes.size := by
--             rw [eq₂, eq₁]
--             simp
--           simp [compile.loop.get_lt rfl this]
--           have : start.val = (nfa.addNode .fail).val.start.val := by
--             rw [eq₂, eq₁]
--           simp [this, eq₁]
--         have rhs : nfa'''[i] = .split nfa''.val.start next := by
--           simp [NFA.eq_get, eq₅, eq₄, eq.symm]
--         simp [lhs, rhs]
--       | isFalse neq =>
--         have : nodes'''[i] = nfa''.val.nodes[i] := by
--           simp [eq₄]
--           apply Array.get_set_ne
--           exact neq
--         simp [NFA.eq_get, eq₅, this]
--     have ih₁ := ih₁ eq₃.symm nfa''' this
--     have ih₂ := ih₂ eq'' nfa''' (le_refl _)

--     rw [evalFrom_append (String.eq_of_append_of_eq_of_append eqs)]
--     suffices next ∈ nfa'''.evalFrom (nfa'''.evalFrom {nfa'''.start.val} s₁.data) s₂.data by
--       have : next ∈ List.foldl nfa'''.stepSet (nfa'''.εClosureSet (nfa'''.evalFrom {nfa'''.start.val} s₁.data)) s₂.data := by
--         exact this
--       simp [εClosureSet_evalFrom] at this
--       exact this
--     apply mem_evalFrom_subset ih₂
--     simp [εClosureSet_evalFrom]

--     have : nfa'''.start.val = start.val := by
--       rw [eq₅]
--     apply mem_evalFrom_subset (this.symm ▸ ih₁)
--     simp
--     apply εClosureSet_singleton_step
--     have : nfa'''[nfa'''.start.val] = .split nfa''.val.start next := by
--       rw [eq₅, NFA.eq_get]
--       simp [eq₄]
--     simp [this, getElem?, Option.εStep, Node.εStep]

-- -- こんな感じのが必要では
-- -- def NFA.evalFromUntil (nfa : NFA) (S : Set Nat) (next : Nat) (s : List Char) : Option (List Char) :=
-- --   if next ∈ S then
-- --     some s
-- --   else
-- --     match s with
-- --     | [] => none
-- --     | c :: s => nfa.evalFromUntil (nfa.stepSet S c) next s

-- def NFA.stepSet' (nfa : NFA) (S : Set Nat) (c : Char) : Set Nat :=
--   ⋃ i ∈ nfa.εClosureSet S, nfa.εClosureSet (nfa[i]?.charStep c)

-- theorem compile.loop.εClosure_subset (eq : compile.loop r next nfa = result)
--   (h : i ∈ NewNodesRange eq) (cls : j ∈ result.val.εClosure i) :
--   j ∈ result.val.εClosure next ∪ NewNodesRange eq := by
--   induction cls with
--   | base => exact Or.inr h
--   | @step i j k head tail ih =>
--     simp [Option.εStep.simp, h.right] at head
--     -- Use whatever char
--     let ⟨_, h⟩ := step_range (c := default) eq i h.left h.right
--     have : j = next ∨ j ∈ NewNodesRange eq := mem_insert_iff.mp (mem_of_mem_of_subset head h)
--     cases this with
--     | inl h => exact mem_union_left _ (h ▸ tail)
--     | inr h => exact ih h

-- theorem compile.loop.εClosureSet_NewNodesRange (eq : compile.loop r next nfa = result) :
--   result.val.εClosureSet (NewNodesRange eq) ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
--   simp [NFA.εClosureSet]
--   intro i h
--   simp [subset_def]
--   intro j cls
--   exact εClosure_subset eq h cls

-- theorem compile.loop.εClosureSet_subset (eq : compile.loop r next nfa = result)
--   (h : S ⊆ {next} ∪ NewNodesRange eq) :
--   result.val.εClosureSet S ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
--   calc result.val.εClosureSet S
--     _ ⊆ result.val.εClosureSet ({next} ∪ NewNodesRange eq) := by
--       apply NFA.εClosureSet_subset
--       . exact le_refl _
--       . exact h
--     _ = result.val.εClosureSet {next} ∪ result.val.εClosureSet (NewNodesRange eq) :=
--       εClosureSet_union_distrib
--     _ ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
--       simp [εClosureSet_NewNodesRange]
--       simp [εClosureSet]

-- theorem compile.loop.stepSet_subset (eq : compile.loop r next nfa = result)
--   (h : S ⊆ NewNodesRange eq) :
--   result.val.stepSet S c ⊆ result.val.εClosure next ∪ NewNodesRange eq := by
--   simp [NFA.stepSet]
--   intro i h'
--   have : i ∈ NewNodesRange eq := mem_of_subset_of_mem h h'
--   have h'' : nfa.nodes.size ≤ i ∧ i < result.val.nodes.size := by
--     simp [NewNodesRange] at this
--     exact this
--   apply εClosureSet_subset eq
--   simp [Option.charStep.simp, h''.right]
--   let ⟨h, _⟩ := step_range c eq i h''.left h''.right
--   exact h

-- inductive NFA.eval (nfa : NFA) : Set Nat → List Char → Set Nat → List Char → Prop where
--   | base : nfa.eval S cs S cs
--   | step (rest : nfa.eval (nfa.stepSet' S c) cs S' cs') : nfa.eval S (c :: cs) S' cs'

-- Maybe we should recurse from the last as we reason about the last step often
inductive NFA.pathIn (nfa : NFA) (start : Nat) : Nat → List Char → Nat → List Char → Prop where
  | base (h : start ≤ i) (eqi : i = j) (eqs : cs = cs') : nfa.pathIn start i cs j cs'
  | charStep {i j k : Nat} {c : Char} {cs cs' : List Char}
    (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size)
    (step : j ∈ nfa[i].charStep c) (rest : nfa.pathIn start j cs k cs') :
    nfa.pathIn start i (c :: cs) k cs'
  | εStep {i j k : Nat} {cs cs' : List Char}
    (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size)
    (step : j ∈ nfa[i].εStep) (rest : nfa.pathIn start j cs k cs') :
    nfa.pathIn start i cs k cs'

theorem le_of_pathIn_left (path : NFA.pathIn nfa start i cs j cs') : start ≤ i := by
  cases path with
  | base h => exact h
  | charStep h₁ => exact h₁
  | εStep h₁ => exact h₁

theorem le_of_pathIn_right (path : NFA.pathIn nfa start i cs j cs') : start ≤ j := by
  induction path with
  | base h eqi => exact eqi ▸ h
  | charStep _ _ _ _ ih => exact ih
  | εStep _ _ _ _ ih => exact ih

theorem NFA.pathIn.cast {nfa nfa' : NFA} (start : Nat)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : NFA.pathIn nfa start i cs j cs') :
  NFA.pathIn nfa' start i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base h eqi eqs
  | charStep h₁ h₂ step _ ih =>
    let ⟨h₂', eq⟩ := eq _ h₁ h₂
    exact .charStep h₁ h₂' (eq ▸ step) ih
  | εStep h₁ h₂ step _ ih =>
    let ⟨h₂', eq⟩ := eq _ h₁ h₂
    exact .εStep h₁ h₂' (eq ▸ step) ih

inductive NFA.pathToNext (nfa : NFA) (next start i : Nat) (cs cs' : List Char) : Prop where
  | charStep (i' : Nat) (h : i' < nfa.nodes.size) (c : Char)
    (step : next ∈ nfa[i'].charStep c) (path : nfa.pathIn start i cs i' (c :: cs'))
  | εStep (i' : Nat) (h : i' < nfa.nodes.size)
    (step : next ∈ nfa[i'].εStep) (path : nfa.pathIn start i cs i' cs')

theorem le_of_pathToNext (path : NFA.pathToNext nfa next start i cs cs') : start ≤ i := by
  cases path with
  | charStep _ _ _ _ path => exact le_of_pathIn_left path
  | εStep _ _ _ path => exact le_of_pathIn_left path

theorem NFA.pathToNext.cons_char {start}
  (h₁ : start ≤ i) (h₂: i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c)
  (path : pathToNext nfa next start j cs cs')
  : pathToNext nfa next start i (c :: cs) cs' := by
  cases path with
  | charStep i' h c step' path => exact .charStep i' h c step' (.charStep h₁ h₂ step path)
  | εStep i' h step' path => exact .εStep i' h step' (.charStep h₁ h₂ step path)

theorem NFA.pathToNext.cons_ε {start}
  (h₁ : start ≤ i) (h₂: i < nfa.nodes.size) (step : j ∈ nfa[i].εStep)
  (path : pathToNext nfa next start j cs cs')
  : pathToNext nfa next start i cs cs' := by
  cases path with
  | charStep i' h c step' path => exact .charStep i' h c step' (.εStep h₁ h₂ step path)
  | εStep i' h step' path => exact .εStep i' h step' (.εStep h₁ h₂ step path)

theorem NFA.pathToNext.cast {nfa nfa' : NFA} {next start i : Nat} {cs cs' : List Char}
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : NFA.pathToNext nfa next start i cs cs') :
  NFA.pathToNext nfa' next start i cs cs' := by
  induction path with
  | charStep i' h c step path =>
    let ⟨h', eq'⟩ := eq _ (le_of_pathIn_right path) h
    exact .charStep i' h' c (eq' ▸ step) (NFA.pathIn.cast start eq path)
  | εStep i' h step path =>
    let ⟨h', eq'⟩ := eq _ (le_of_pathIn_right path) h
    exact .εStep i' h' (eq' ▸ step) (NFA.pathIn.cast start eq path)

inductive NFA.starLoop (eq : compile.loop (.star r) next nfa = result) : List Char → List Char → Prop where
  | complete (eqs : cs = cs') : starLoop eq cs cs'
  | loop (eqr : result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split rStart next)
    (path : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) rStart cs cs'')
    (rest : NFA.starLoop eq cs'' cs') : starLoop eq cs cs'

theorem eqr_of_mem_of_le (eq : compile.loop (.star r) next nfa = result)
  (prem₁ : next < nfa.nodes.size)
  (mem : rStart ∈ (result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq)).εStep)
  (le : nfa.nodes.size + 1 ≤ rStart) :
  result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split rStart next := by
  -- have : result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split j' next := by
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
  | @charStep i j k c cs cs' h₁ h₂ step _ ih =>
    have ne : i ≠ nfa.nodes.size := by
      intro eq'
      simp [eq', compile.loop.star.charStep_loopStartNode eq] at step
    simp [ne]
    have assm₁' : j < result.val.nodes.size :=
      show j ∈ { j | j < result.val.nodes.size } from
        Set.mem_of_mem_of_subset step ((prem₂ ⟨i, assm₁⟩).left c)
    have h₁' : nfa.nodes.size + 1 ≤ i := Nat.lt_of_le_of_ne h₁ ne.symm
    have ih := ih assm₁' assm₂
    split at ih
    next h =>
      cases ih with
      | inl eqs =>
        exists cs
        exact ⟨.charStep i assm₁ c (h ▸ step) (.base h₁' rfl rfl), .complete eqs⟩
      | inr cond =>
        let ⟨j', cs'', _, h', path', l⟩ := cond
        refine ⟨cs, ?_, ?_⟩
        . exact .charStep i assm₁ c (h ▸ step) (.base h₁' rfl rfl)
        . have : result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split j' next :=
            eqr_of_mem_of_le eq prem₁ (h ▸ h') (le_of_pathToNext path')
          exact .loop this path' l
    next h =>
      let ⟨cs'', path, l⟩ := ih
      refine ⟨cs'', ?_, l⟩
      exact pathToNext.cons_char h₁' assm₁ step path
  | @εStep i j k cs cs' h₁ h₂ step rest ih =>
    have assm₁' : j < result.val.nodes.size :=
      show j ∈ { j | j < result.val.nodes.size } from
        Set.mem_of_mem_of_subset step ((prem₂ ⟨i, assm₁⟩).right)
    have ih := ih assm₁' assm₂
    cases Nat.lt_or_eq_of_le h₁ with
    | inl lt =>
      have ne : i ≠ nfa.nodes.size := Nat.ne_of_gt lt
      simp [ne]
      -- TODO: This is mostly duplicate of above. I feel we should have a step prop and
      -- not prepare separate constructors for charStep and εStep
      have h₁' : nfa.nodes.size + 1 ≤ i := Nat.lt_of_le_of_ne h₁ ne.symm
      split at ih
      next h =>
        cases ih with
        | inl eqs =>
          exists cs
          exact ⟨.εStep i assm₁ (h ▸ step) (.base h₁' rfl rfl), .complete eqs⟩
        | inr cond =>
          let ⟨j', cs'', _, h', path', l⟩ := cond
          refine ⟨cs, ?_, ?_⟩
          . exact .εStep i assm₁ (h ▸ step) (.base h₁' rfl rfl)
          . have : result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split j' next :=
              eqr_of_mem_of_le eq prem₁ (h ▸ h') (le_of_pathToNext path')
            exact .loop this path' l
      next h =>
        let ⟨cs'', path, l⟩ := ih
        refine ⟨cs'', ?_, l⟩
        exact pathToNext.cons_ε h₁' assm₁ step path
    | inr eq =>
      subst eq
      simp
      let ⟨rStart, range, node⟩ := compile.loop.star.loopStartNode eq
      simp at range
      have eqj : j = rStart := by
        simp [node, Node.εStep] at step
        cases step with
        | inl eq => exact eq
        | inr eq =>
          have : nfa.nodes.size ≤ next := eq ▸ le_of_pathIn_left rest
          exact ((Nat.not_lt_of_ge this) prem₁).elim
      have neq : rStart ≠ nfa.nodes.size := by
        apply Nat.ne_of_gt
        exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) range.left
      simp [eqj, neq] at ih
      exact .inr ⟨rStart, range.right, eqj ▸ step, ih⟩

theorem NFA.starLoop.intro (eq : compile.loop (.star r) next nfa = result)
  (prem₁ : next < nfa.nodes.size) (prem₂ : result.val.inBounds)
  (ev : pathIn result nfa.nodes.size nfa.nodes.size cs nfa.nodes.size cs') :
  starLoop eq cs cs' := by
  have : nfa.nodes.size < result.val.nodes.size := compile.loop.star.lt_size eq
  let loop := starLoop.intro' eq prem₁ prem₂ this rfl ev
  simp at loop
  match loop with
  | .inl eqs => exact .complete eqs
  | .inr ⟨rStart, _, step, ⟨_, path, loop⟩⟩ =>
    have : result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split rStart next :=
        eqr_of_mem_of_le eq prem₁ step (le_of_pathToNext path)
    exact .loop this path loop

theorem matches_prefix_of_starLoop (eq : compile.loop (.star r) next nfa = result)
  (mr : ∀ {cs cs'} rStart,
    result.val[Array.size nfa.nodes]'(compile.loop.star.lt_size eq) = Node.split rStart next →
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

theorem matches_prefix_of_eval (eq : compile.loop r next nfa = result)
  (h₁ : next < nfa.nodes.size) (h₂ : nfa.inBounds)
  (ev : NFA.pathToNext result next nfa.nodes.size result.val.start.val s s') :
  ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
  induction r generalizing next nfa s s' with
  | empty => sorry
  | epsilon => sorry
  | char c => sorry
  | alternate r₁ r₂ ih₁ ih₂ =>
    sorry
    -- apply compile.loop.alternate eq
    -- intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ eq₃ eq₄ eq₅ eq

    -- have inBounds₁ := compile.loop.inBounds eq₁.symm h₁ h₂
    -- have inBounds₂ :=
    --   compile.loop.inBounds eq₃.symm (Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₁.property)) inBounds₁
    -- have size₁ : next < nfa₁.val.nodes.size := Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₁.property)

    -- rw [eq] at ev
    -- simp at ev

    -- cases ev with
    -- | base eqi =>
    --   have : final.val.start.val ≠ next := by
    --     apply Nat.ne_of_gt
    --     calc next
    --       _ < nfa.nodes.size := h₁
    --       _ ≤ nfa₂.val.nodes.size := NFA.le_size_of_le (NFA.le_trans nfa₁.property nfa₂.property)
    --       _ = _ := by
    --         rw [eq₅]
    --         simp [NFA.addNode]
    --   contradiction
    -- | @charStep _ j _ c _ _ _ step =>
    --   have : final.val[final.val.start].charStep c = ∅ := by
    --     rw [eq₅]
    --     simp [Node.charStep]
    --   have : j ∈ ∅ := this ▸ step
    --   exact this.elim
    -- | @εStep i j k cs cs' h step rest =>
    --   have : j = start₁.val ∨ j = start₂.val := by
    --     subst eq₅
    --     simp [Node.εStep] at step
    --     exact step
    --   have ev₂ : nfa₂ ⊢ (j, s) ⟶* (next, s') := by
    --     apply eval_of_eval_addNode eq₅.symm _ inBounds₂ rest
    --     cases this with
    --     | inl h =>
    --       have lt₁ : start₁ < nfa₂.val.nodes.size :=
    --         Nat.lt_of_lt_of_le start₁.isLt (NFA.le_size_of_le nfa₂.property)
    --       simp [h, lt₁]
    --     | inr h => simp [h]
    --   cases this with
    --   | inl step₁ =>
    --     have ev₁ : nfa₁ ⊢ (j, s) ⟶* (next, s') := by
    --       apply eval_of_eval_compile eq₃.symm _ inBounds₁ ev₂
    --       simp [step₁]
    --     let ⟨p, eqs, m₁⟩ := ih₁ eq₁.symm h₁ h₂ (eq₂ ▸ step₁ ▸ ev₁)
    --     exact ⟨p, eqs, .alternateLeft m₁⟩
    --   | inr step₂ =>
    --     let ⟨p, eqs, m₂⟩ := ih₂ eq₃.symm size₁ inBounds₁ (eq₄ ▸ step₂ ▸ ev₂)
    --     exact ⟨p, eqs, .alternateRight m₂⟩
  | concat r₁ r₂ ih₁ ih₂ =>
    sorry
    -- apply compile.loop.concat eq
    -- intro nfa₂ nfa₁ property eq₂ eq₁ eq

    -- have inBounds₂ := compile.loop.inBounds eq₂.symm h₁ h₂
    -- have inBounds₁ := compile.loop.inBounds eq₁.symm nfa₂.val.start.isLt inBounds₂

    -- rw [eq] at ev
    -- simp at ev
    -- have : next < nfa₂.val.nodes.size := Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₂.property)
    -- let ⟨s₂s', ev₁, ev'⟩ := eval_to_next_of_eval_from_start eq₁.symm this ev
    -- let ⟨s₁, eqs₁, m₁⟩ := ih₁ eq₁.symm nfa₂.val.start.isLt inBounds₂ ev₁

    -- have ev₂ : nfa₂ ⊢ (nfa₂.val.start, s₂s') ⟶* (next, s') :=
    --   eval_of_eval_compile eq₁.symm nfa₂.val.start.isLt inBounds₂ ev'
    -- let ⟨s₂, eqs₂, m₂⟩ := ih₂ eq₂.symm h₁ h₂ ev₂

    -- exact ⟨s₁ ++ s₂, by simp [eqs₁, eqs₂], .concat ⟨s₁ ++ s₂⟩ ⟨s₁⟩ ⟨s₂⟩ r₁ r₂ rfl m₁ m₂⟩
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
        exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) (NFA.le_size_of_le placeholder.property)
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
    rw [eqStart] at ev

    have eqSize : result.val.nodes.size = compiled.val.nodes.size := by
      simp [eq', eq₅, eq₄]
    have firstNode : result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq) = .split compiled.val.start next := by
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
      (eqr : result.val[Array.size nfa.nodes]'(compile.loop.star.lt_size eq) = Node.split rStart next)
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
    have ih (s s' : List Char) := ih (s := s) (s' := s') eq₃.symm loopStart.isLt placeholder.inBounds

    cases ev with
    | charStep i' h c step path =>
      -- No nodes can perform charStep to `next`.
      cases Nat.eq_or_lt_of_le (le_of_pathIn_right path) with
      | inl eq => simp [eq.symm, firstNode, Node.charStep] at step
      | inr lt => exact absurd step ((compiledNodesRange i' lt h).left c)
    | εStep i' h step path =>
      -- Only the loop start can perform εStep to `next`.
      have : i' = nfa.nodes.size := by
        cases Nat.eq_or_lt_of_le (le_of_pathIn_right path) with
        | inl eq => exact eq.symm
        | inr lt => exact absurd step (compiledNodesRange i' lt h).right
      subst this
      have loop := NFA.starLoop.intro eq h₁ inBounds' path
      exact matches_prefix_of_starLoop eq mr loop

-- inductive NFA.eval (nfa : NFA) : Nat → List Char → Nat → List Char → Prop where
--   | base (eqi : i = j) (eqs : cs = cs') : nfa.eval i cs j cs'
--   | charStep {i j k : Nat} {c : Char} {cs cs' : List Char}
--     (h : i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c) (rest : nfa.eval j cs k cs') :
--     nfa.eval i (c :: cs) k cs'
--   | εStep {i j k : Nat} {cs cs' : List Char}
--     (h : i < nfa.nodes.size) (step : j ∈ nfa[i].εStep) (rest : nfa.eval j cs k cs') :
--     nfa.eval i cs k cs'

-- -- TODO: is this useful?
-- theorem NFA.eval_prefix {nfa : NFA} (ev : nfa.eval i s j s₂) :
--   ∃s₁, s = s₁ ++ s₂ := by
--   induction ev with
--   | base => exists []
--   | @charStep _ _ _ c _ _ _ _ _ ih =>
--     let ⟨s₁', h⟩ := ih
--     exists c :: s₁'
--     simp [h]
--   | εStep _ _ _ ih => exact ih

-- notation:65 nfa " ⊢ (" i ", " s ") ⟶* (" j ", " s' ")" => NFA.eval nfa i s j s'

-- theorem eval_last {nfa : NFA} (inBounds : nfa.inBounds) (ev : nfa ⊢ (i, s) ⟶* (k, s')) :
--   (i = k ∧ s = s') ∨
--   (∃ (j : Fin nfa.nodes.size) (c : Char), nfa ⊢ (i, s) ⟶* (j, c :: s') ∧ k ∈ nfa[j].charStep c) ∨
--   (∃ (j : Fin nfa.nodes.size), nfa ⊢ (i, s) ⟶* (j, s') ∧ k ∈ nfa[j].εStep) := by
--   induction ev with
--   | base eqi eqs => exact .inl ⟨eqi, eqs⟩
--   | @charStep i j k c cs cs' h step _ ih =>
--     match ih with
--     | .inl ⟨eqj, eqs⟩ => exact .inr (.inl ⟨⟨i, h⟩, c, .base rfl (by simp [eqs]), eqj ▸ step⟩)
--     | .inr (.inl ⟨j', c', ev', step'⟩) => exact .inr (.inl ⟨j', c', .charStep h step ev', step'⟩)
--     | .inr (.inr ⟨j', ev', step'⟩) => exact .inr (.inr ⟨j', .charStep h step ev', step'⟩)
--   | @εStep i j k cs cs' h step _ ih =>
--     match ih with
--     | .inl ⟨eqj, eqs⟩ => exact .inr (.inr ⟨⟨i, h⟩, .base rfl (by simp [eqs]), eqj ▸ step⟩)
--     | .inr (.inl ⟨j', c', ev', step'⟩) => exact .inr (.inl ⟨j', c', .εStep h step ev', step'⟩)
--     | .inr (.inr ⟨j', ev', step'⟩) => exact .inr (.inr ⟨j', .εStep h step ev', step'⟩)

-- theorem eval_trans {nfa : NFA} (ev₁ : nfa ⊢ (i, s) ⟶* (j, s')) (ev₂ : nfa ⊢ (j, s') ⟶* (k, s'')) :
--   nfa ⊢ (i, s) ⟶* (k, s'') := by
--   induction ev₁ with
--   | base eqi eqs => rw [eqi, eqs]; exact ev₂
--   | charStep h step _ ih => exact .charStep h step (ih ev₂)
--   | εStep h step _ ih => exact .εStep h step (ih ev₂)

-- theorem eval_inBounds {nfa : NFA} (inBounds : nfa.inBounds) (h : i < nfa.nodes.size)
--   (ev : nfa ⊢ (i, s) ⟶* (j, s')) : j < nfa.nodes.size := by
--   induction ev with
--   | base eqi => exact eqi ▸ h
--   | @charStep i j _ c _ _ h' step _ ih =>
--     apply ih
--     show j ∈ { j | j < nfa.nodes.size }
--     exact mem_of_mem_of_subset step ((inBounds ⟨i, h'⟩).left c)
--   | @εStep i j _ _ _ h' step _ ih =>
--     apply ih
--     show j ∈ { j | j < nfa.nodes.size }
--     exact mem_of_mem_of_subset step (inBounds ⟨i, h'⟩).right

-- -- When we expand the NFA by appending nodes, the evaluation relation is preserved in the original range.

-- theorem eval_ge_of_get_lt {nfa nfa' : NFA} (le : nfa.nodes.size ≤ nfa'.nodes.size)
--   (get_lt : ∀ {i}, (h : i < nfa.nodes.size) → nfa'[i]'(Nat.lt_of_lt_of_le h le) = nfa[i])
--   (ev : nfa ⊢ (i, s) ⟶* (j, s')) :
--   nfa' ⊢ (i, s) ⟶* (j, s') := by
--   induction ev with
--   | base eqi eqs => exact .base eqi eqs
--   | charStep h step _ ih =>
--     have eqi := get_lt h
--     exact .charStep
--       (Nat.lt_of_lt_of_le h le) (eqi.symm ▸ step) ih
--   | εStep h step _ ih =>
--     have eqi := get_lt h
--     exact .εStep
--       (Nat.lt_of_lt_of_le h le) (eqi.symm ▸ step) ih

-- theorem eval_le_of_get_lt {nfa nfa' : NFA} (le : nfa.nodes.size ≤ nfa'.nodes.size)
--   (get_lt : ∀ {i}, (h : i < nfa.nodes.size) → nfa'[i]'(Nat.lt_of_lt_of_le h le) = nfa[i])
--   (h₁ : i < nfa.nodes.size) (h₂ : nfa.inBounds) (ev : nfa' ⊢ (i, s) ⟶* (j, s')) :
--   nfa ⊢ (i, s) ⟶* (j, s') := by
--   induction ev with
--   | base eqi eqs => exact .base eqi eqs
--   | @charStep i j _ c _ _ _ step _ ih =>
--     have eqi := get_lt h₁
--     rw [eqi] at step
--     have : j < nfa.nodes.size := show j ∈ { j | j < nfa.nodes.size } by
--       exact mem_of_mem_of_subset step ((h₂ ⟨i, h₁⟩).left c)
--     exact .charStep h₁ step (ih this)
--   | @εStep i j _ _ _ _ step _ ih =>
--     have eqi := get_lt h₁
--     rw [eqi] at step
--     have : j < nfa.nodes.size := show j ∈ { j | j < nfa.nodes.size } by
--       exact mem_of_mem_of_subset step (h₂ ⟨i, h₁⟩).right
--     exact .εStep h₁ step (ih this)

-- theorem eval_addNode_of_eval (eq : NFA.addNode nfa node = result)
--   (ev : nfa ⊢ (i, s) ⟶* (j, s')) : result ⊢ (i, s) ⟶* (j, s') :=
--   eval_ge_of_get_lt (NFA.le_size_of_le result.property) (fun h => eq ▸ NFA.get_lt_addNode h) ev

-- theorem eval_compile_of_eval (eq : compile.loop r next nfa = result)
--   (ev : nfa ⊢ (i, s) ⟶* (j, s')) : result ⊢ (i, s) ⟶* (j, s') :=
--   eval_ge_of_get_lt (NFA.le_size_of_le result.property) (compile.loop.get_lt eq) ev

-- theorem eval_of_eval_addNode (eq : NFA.addNode nfa node = result)
--   (h₁ : i < nfa.nodes.size) (h₂ : nfa.inBounds)
--   (ev : result ⊢ (i, s) ⟶* (j, s')) : nfa ⊢ (i, s) ⟶* (j, s') :=
--   eval_le_of_get_lt (NFA.le_size_of_le result.property) (fun h => eq ▸ NFA.get_lt_addNode h) h₁ h₂ ev

-- theorem eval_of_eval_compile (eq : compile.loop r next nfa = result)
--   (h₁ : i < nfa.nodes.size) (h₂ : nfa.inBounds)
--   (ev : result ⊢ (i, s) ⟶* (j, s')) : nfa ⊢ (i, s) ⟶* (j, s') :=
--   eval_le_of_get_lt (NFA.le_size_of_le result.property) (compile.loop.get_lt eq) h₁ h₂ ev

-- -- The compiled NFA first circulates within the new nodes range,
-- -- then it must go to the next node before escaping to the original range.

-- theorem eval_to_next_of_eval (eq : compile.loop r next nfa = result)
--   (h₁ : i ∈ compile.loop.NewNodesRange eq) (h₂ : k < nfa.nodes.size)
--   (ev : result ⊢ (i, s) ⟶* (k, s'')) :
--   ∃ s', result ⊢ (i, s) ⟶* (next, s') ∧ result ⊢ (next, s') ⟶* (k, s'') := by
--   induction ev with
--   | base eqi =>
--     simp [compile.loop.NewNodesRange] at h₁
--     exact (Nat.not_lt_of_ge h₁.left (eqi.symm ▸ h₂)).elim
--   | @charStep i j k c cs cs' h step rest ih =>
--     have mem : j ∈ {next} ∪ compile.loop.NewNodesRange eq := by
--       apply mem_of_mem_of_subset step
--       exact (compile.loop.step_range c eq i h₁.left h₁.right).left
--     cases Nat.decEq j next with
--     | isTrue eq =>
--       rw [←eq]
--       exact ⟨cs, .charStep h step (.base rfl rfl), rest⟩
--     | isFalse neq =>
--       have : j ∈ compile.loop.NewNodesRange eq := Set.mem_of_mem_insert_of_ne mem neq
--       let ⟨s', ih₁, ih₂⟩ := ih this h₂
--       exact ⟨s', .charStep h step ih₁, ih₂⟩
--   | @εStep i j k cs cs' h step rest ih =>
--     have mem : j ∈ {next} ∪ compile.loop.NewNodesRange eq := by
--       apply mem_of_mem_of_subset step
--       exact (compile.loop.step_range default eq i h₁.left h₁.right).right
--     cases Nat.decEq j next with
--     | isTrue eq =>
--       rw [←eq]
--       exact ⟨cs, .εStep h step (.base rfl rfl), rest⟩
--     | isFalse neq =>
--       have : j ∈ compile.loop.NewNodesRange eq := Set.mem_of_mem_insert_of_ne mem neq
--       let ⟨s', ih₁, ih₂⟩ := ih this h₂
--       exact ⟨s', .εStep h step ih₁, ih₂⟩

-- theorem eval_to_next_of_eval_from_start (eq : compile.loop r next nfa = result)
--   (h : k < nfa.nodes.size) (ev : result ⊢ (result.val.start, s) ⟶* (k, s'')) :
--   ∃ s', result ⊢ (result.val.start, s) ⟶* (next, s') ∧ result ⊢ (next, s') ⟶* (k, s'') := by
--   have h₁ : result.val.start.val ∈ compile.loop.NewNodesRange eq := compile.loop.start_in_NewNodesRange eq
--   exact eval_to_next_of_eval eq h₁ h ev

-- /--
--   An inductive predicate that represents the "loop" behavior of the star operator.

--   NOTE: this definition assumes that `loopStart` corresponds to `nfa.nodes.size`.
-- -/
-- inductive evalStar (eq : compile.loop (.star r) next nfa = result) : List Char → List Char → Prop where
--   | complete (eqs : s = s') : evalStar eq s s'
--   | step
--     (step : compile.loop.star.rStart eq ∈ (result.val[nfa.nodes.size]'(compile.loop.star.lt_size eq)).εStep)
--     (ev : result ⊢ (compile.loop.star.rStart eq, s) ⟶* (nfa.nodes.size, s''))
--     (rest : evalStar eq s'' s') : evalStar eq s s'

-- theorem evalStar.eval {eq : compile.loop (.star r) next nfa = result}
--   (evStar : evalStar eq s s') :
--   result ⊢ (nfa.nodes.size, s) ⟶* (nfa.nodes.size, s') := by
--   induction evStar with
--   | complete eqs => exact .base rfl eqs
--   | step step ev _ ih =>
--     exact eval_trans (.εStep (compile.loop.star.lt_size eq) step ev) ih

-- theorem evalStar.intro' (eq : compile.loop (.star r) next nfa = result)
--   (h₁ : next < nfa.nodes.size) (h₂ : nfa.inBounds)
--   (assm₁ : start < result.val.nodes.size - 1)
--   (ev : result ⊢ (start, s) ⟶* (last, s')) :
--   ∃ p s'', s = p ++ s'' ∧ result ⊢ (start, s) ⟶* (last, s'') ∧ evalStar eq s'' s' := by
--   induction ev with
--   | @base i j s s' eqi eqs => exact ⟨[], s', by simp [eqs], .base eqi eqs, .complete rfl⟩
--   | @charStep _ j _ c _ _ h step _ ih =>
--     let inBounds := compile.loop.inBounds.star.compiled eq h₁ h₂ assm₁
--     have assm₁' : j < result.val.nodes.size - 1 :=
--       show j ∈ { j | j < result.val.nodes.size - 1 } by
--         exact mem_of_mem_of_subset step (inBounds.left c)
--     let ⟨p, s'', eqs, ev, rest⟩ := ih assm₁'
--     exact ⟨c :: p, s'', by simp [eqs], .charStep h step ev, rest⟩
--   | @εStep _ j _ _ _ h step _ ih =>
--     let inBounds := compile.loop.inBounds.star.compiled eq h₁ h₂ assm₁
--     have assm₁' : j < result.val.nodes.size - 1 :=
--       show j ∈ { j | j < result.val.nodes.size - 1 } by
--         exact mem_of_mem_of_subset step inBounds.right
--     let ⟨p, s'', eqs, ev, rest⟩ := ih assm₁'
--     exact ⟨p, s'', by simp [eqs], .εStep h step ev, rest⟩

-- theorem evalStar.intro (eq : compile.loop (.star r) next nfa = result)
--   (h₁ : next < nfa.nodes.size) (h₂ : nfa.inBounds)
--   (ev : result ⊢ (nfa.nodes.size, s) ⟶* (nfa.nodes.size, s')) :
--   evalStar eq s s' := by
--   apply compile.loop.star eq
--   intro placeholder loopStart compiled nodes patched final isLt isLt' property'
--     eq₁ _ _ eq₄ eq₅ eq₆ eq'
--   have : nfa.nodes.size < result.val.nodes.size - 1 := by
--     simp [eq', eq₆, NFA.addNode, eq₅, eq₄]
--     calc nfa.nodes.size
--       _ < placeholder.val.nodes.size := by simp [eq₁, NFA.addNode]
--       _ ≤ compiled.val.nodes.size := NFA.le_size_of_le compiled.property
--   let ⟨_, s'', _, ev', evStar⟩ := evalStar.intro' eq h₁ h₂ this ev

--   have loopStartNode := compile.loop.star.loopStartNode eq
--   cases ev' with
--   | base _ eqs => exact eqs.symm ▸ evStar
--   | charStep _ step => simp [loopStartNode, Node.charStep] at step
--   | @εStep _ j _ cs cs' h step ev'' =>
--     simp [loopStartNode, Node.εStep] at step
--     cases step with
--     | inl h =>
--       have ev'' : ↑result ⊢ (compile.loop.star.rStart eq, s) ⟶* (Array.size nfa.nodes, s'') := h ▸ ev''
--       exact .step (by simp [loopStartNode, Node.εStep]) ev'' evStar
--     | inr h =>
--       have ev'' : nfa ⊢ (j, s) ⟶* (nfa.nodes.size, s'') :=
--         eval_of_eval_compile eq (h ▸ h₁) h₂ ev''
--       have : nfa.nodes.size < nfa.nodes.size := eval_inBounds h₂ h₁ (h ▸ ev'')
--       exact (Nat.lt_irrefl _ this).elim

-- theorem matches_prefix_of_evalStar {eq : compile.loop (.star r) next nfa = result}
--   (evStar : evalStar eq s s')
--   (mr : ∀ s s', result ⊢ (compile.loop.star.rStart eq, s) ⟶* (nfa.nodes.size, s') →
--     ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩) :
--   ∃ p, s = p ++ s' ∧ Regex.matches ⟨p⟩ (Regex.star r) := by
--   induction evStar with
--   | complete eqs => exact ⟨[], by simp [eqs], .starEpsilon rfl⟩
--   | step _ ev _ ih =>
--     let ⟨p₁, eqs₁, m₁⟩ := mr _ _ ev
--     let ⟨p₂, eqs₂, m₂⟩ := ih
--     exact ⟨p₁ ++ p₂, by simp [eqs₁, eqs₂], .starConcat _ _ _ _ rfl m₁ m₂⟩

-- theorem matches_prefix_of_eval (eq : compile.loop r next nfa = nfa')
--   (h₁ : next < nfa.nodes.size) (h₂ : nfa.inBounds)
--   (ev : nfa' ⊢ (nfa'.val.start, s) ⟶* (next, s')) :
--   ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
--   induction r generalizing next nfa s s' with
--   | empty => sorry
--   | epsilon => sorry
--   | char c => sorry
--   | alternate r₁ r₂ ih₁ ih₂ =>
--     apply compile.loop.alternate eq
--     intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ eq₃ eq₄ eq₅ eq

--     have inBounds₁ := compile.loop.inBounds eq₁.symm h₁ h₂
--     have inBounds₂ :=
--       compile.loop.inBounds eq₃.symm (Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₁.property)) inBounds₁
--     have size₁ : next < nfa₁.val.nodes.size := Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₁.property)

--     rw [eq] at ev
--     simp at ev

--     cases ev with
--     | base eqi =>
--       have : final.val.start.val ≠ next := by
--         apply Nat.ne_of_gt
--         calc next
--           _ < nfa.nodes.size := h₁
--           _ ≤ nfa₂.val.nodes.size := NFA.le_size_of_le (NFA.le_trans nfa₁.property nfa₂.property)
--           _ = _ := by
--             rw [eq₅]
--             simp [NFA.addNode]
--       contradiction
--     | @charStep _ j _ c _ _ _ step =>
--       have : final.val[final.val.start].charStep c = ∅ := by
--         rw [eq₅]
--         simp [Node.charStep]
--       have : j ∈ ∅ := this ▸ step
--       exact this.elim
--     | @εStep i j k cs cs' h step rest =>
--       have : j = start₁.val ∨ j = start₂.val := by
--         subst eq₅
--         simp [Node.εStep] at step
--         exact step
--       have ev₂ : nfa₂ ⊢ (j, s) ⟶* (next, s') := by
--         apply eval_of_eval_addNode eq₅.symm _ inBounds₂ rest
--         cases this with
--         | inl h =>
--           have lt₁ : start₁ < nfa₂.val.nodes.size :=
--             Nat.lt_of_lt_of_le start₁.isLt (NFA.le_size_of_le nfa₂.property)
--           simp [h, lt₁]
--         | inr h => simp [h]
--       cases this with
--       | inl step₁ =>
--         have ev₁ : nfa₁ ⊢ (j, s) ⟶* (next, s') := by
--           apply eval_of_eval_compile eq₃.symm _ inBounds₁ ev₂
--           simp [step₁]
--         let ⟨p, eqs, m₁⟩ := ih₁ eq₁.symm h₁ h₂ (eq₂ ▸ step₁ ▸ ev₁)
--         exact ⟨p, eqs, .alternateLeft m₁⟩
--       | inr step₂ =>
--         let ⟨p, eqs, m₂⟩ := ih₂ eq₃.symm size₁ inBounds₁ (eq₄ ▸ step₂ ▸ ev₂)
--         exact ⟨p, eqs, .alternateRight m₂⟩
--   | concat r₁ r₂ ih₁ ih₂ =>
--     apply compile.loop.concat eq
--     intro nfa₂ nfa₁ property eq₂ eq₁ eq

--     have inBounds₂ := compile.loop.inBounds eq₂.symm h₁ h₂
--     have inBounds₁ := compile.loop.inBounds eq₁.symm nfa₂.val.start.isLt inBounds₂

--     rw [eq] at ev
--     simp at ev
--     have : next < nfa₂.val.nodes.size := Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₂.property)
--     let ⟨s₂s', ev₁, ev'⟩ := eval_to_next_of_eval_from_start eq₁.symm this ev
--     let ⟨s₁, eqs₁, m₁⟩ := ih₁ eq₁.symm nfa₂.val.start.isLt inBounds₂ ev₁

--     have ev₂ : nfa₂ ⊢ (nfa₂.val.start, s₂s') ⟶* (next, s') :=
--       eval_of_eval_compile eq₁.symm nfa₂.val.start.isLt inBounds₂ ev'
--     let ⟨s₂, eqs₂, m₂⟩ := ih₂ eq₂.symm h₁ h₂ ev₂

--     exact ⟨s₁ ++ s₂, by simp [eqs₁, eqs₂], .concat ⟨s₁ ++ s₂⟩ ⟨s₁⟩ ⟨s₂⟩ r₁ r₂ rfl m₁ m₂⟩
--   | star r ih =>
--     apply compile.loop.star eq
--     intro placeholder loopStart compiled nodes patched final isLt isLt' property'
--       eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq'

--     have placeholder.inBounds : placeholder.val.inBounds := by
--       intro i
--       cases Nat.lt_or_ge i nfa.nodes.size with
--       | inl lt =>
--         have : placeholder.val[i] = nfa[i] := by
--           simp [eq₁, NFA.get_lt_addNode lt]
--         rw [this]
--         exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) (NFA.le_size_of_le placeholder.property)
--       | inr ge =>
--         have : i < nfa.nodes.size + 1 := by
--           have : i < placeholder.val.nodes.size := i.isLt
--           simp [eq₁, NFA.addNode] at this
--           exact this
--         have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge this
--         have : placeholder.val[i] = .fail := by
--           simp [eq₁, this]
--         rw [this]
--         simp
--     have inBounds' : nfa'.val.inBounds := compile.loop.inBounds eq h₁ h₂
--     have firstNode : nfa'.val[nfa'.val.start.val] = .split loopStart loopStart := by
--       simp [eq']
--       have : nfa'.val.start.val = patched.nodes.size := by
--         rw [eq']
--         simp
--         rw [eq₆]
--         simp [NFA.addNode]
--       simp [this]
--       simp [eq₆]

--     have eqRStart : compile.loop.star.rStart eq = compiled.val.start := by
--       simp [compile.loop.star.rStart]
--       sorry
--     -- NOTE: This does not work as `ev` can represent two or more loops.
--     have mr (s s' : List Char) (ev : nfa' ⊢ (compile.loop.star.rStart eq, s) ⟶* (nfa.nodes.size, s')) :
--       ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
--       apply ih eq₃.symm loopStart.isLt placeholder.inBounds
--       simp [eq₂, NFA.start_addNode eq₁.symm]
--       rw [eqRStart, eq'] at ev
--       simp at ev
--       have : patched ⊢ (compiled.val.start, s) ⟶* (nfa.nodes.size, s') :=
--         eval_of_eval_addNode eq₆.symm (Nat.lt_of_lt_of_le compiled.val.start.isLt sorry) sorry ev
--       sorry

--     -- The last step must be an εStep from `loopStart`.
--     match eval_last inBounds' ev with
--     | .inl ⟨eqi, _⟩ =>
--       -- contradiction
--       sorry
--     -- TODO: here, we want to establish that `next` can be reached only by εStep from the split node.
--     -- Then, we can eliminate the charStep case. For the εStep case, we now have the "loop" evaluation.
--     -- We'll construct evalStar from the loop evaluation and induct on it.
--     | .inr (.inl _) => sorry
--     | .inr (.inr ⟨last, evLast, stepLast⟩) =>
--       -- TODO: We'll use the fact that no other nodes have an edge to `nfa.start`.
--       -- TODO: We'll need a precondition that states `nfa` doesn't have an edge to `next`.
--       have : last.val = loopStart.val := sorry
--       rw [this] at evLast
--       -- The first step must be an εStep from `nfa'.val.start` to `loopStart`.
--       cases evLast with
--       | base eqi =>
--         have : loopStart.val < placeholder.val.nodes.size := loopStart.isLt
--         have : loopStart.val ≥ placeholder.val.nodes.size :=
--           calc loopStart.val
--             _ = nfa'.val.start.val := eqi.symm
--             _ = compiled.val.nodes.size := by
--               rw [eq']
--               simp
--               rw [eq₆]
--               simp [NFA.addNode, eq₅, eq₄]
--             _ ≥ placeholder.val.nodes.size := NFA.le_size_of_le compiled.property
--         exact ((Nat.not_lt_of_ge this) (by assumption)).elim
--       | charStep _ stepFirst =>
--         simp [firstNode, Node.charStep] at stepFirst
--       | εStep _ stepFirst evLoop =>
--         simp [firstNode, Node.εStep] at stepFirst
--         subst stepFirst
--         have evLoop : nfa' ⊢ (nfa.nodes.size, s) ⟶* (nfa.nodes.size, s') := by
--           simp [eq₂] at evLoop
--           rw [eq₁] at evLoop
--           simp [NFA.addNode] at evLoop
--           exact evLoop
--         let evStar := evalStar.intro eq h₁ h₂ evLoop
--         exact matches_prefix_of_evalStar evStar mr

end NFA
