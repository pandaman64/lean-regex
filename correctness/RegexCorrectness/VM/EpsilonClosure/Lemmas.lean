import RegexCorrectness.Data.SparseSet
import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure.Basic

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.NFA (εStep')
open String (Pos)

namespace Regex.VM.εClosure

namespace pushNext

variable {s : String} {σ : Strategy s} {nfa : NFA} {pos : Pos s} {node : NFA.Node}
  {inBounds : node.inBounds nfa.nodes.size} {update : σ.Update} {stack : εStack σ nfa}

theorem mem_of_mem_stack {entry} (mem : entry ∈ stack) :
  entry ∈ pushNext σ nfa pos node inBounds update stack := by
  cases node, inBounds, update, stack using pushNext.fun_cases' σ nfa pos <;> grind

end pushNext

-- Theorems that hold for any strategy
section

variable {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {pos : Pos s}
  {matched : Option σ.Update} {next : SearchState σ nfa} {stack : εStack σ nfa}
  {matched' : Option σ.Update} {next' : SearchState σ nfa}

theorem subset (h : εClosure σ nfa wf pos matched next stack = (matched', next')) :
  next.states ⊆ next'.states := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next =>
    simp only [base, Prod.mk.injEq] at h
    simpa [h] using SparseSet.subset_self
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    exact ih h
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    have subset : states' ⊆ next'.states := ih h
    exact SparseSet.subset_trans SparseSet.subset_insert subset

theorem mem_next_of_mem_stack {entry} (h : εClosure σ nfa wf pos matched next stack = (matched', next'))
  (mem_stack : entry ∈ stack) :
  entry.2 ∈ next'.states := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next => simp at mem_stack
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    simp at mem_stack
    match mem_stack with
    | .inl eq =>
      simp [eq]
      have subset := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset mem subset
    | .inr mem => exact ih h mem
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    simp at mem_stack
    match mem_stack with
    | .inl eq =>
      simp [eq]
      have subset := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset (SparseSet.mem_insert mem) subset
    | .inr mem => exact ih h (pushNext.mem_of_mem_stack mem)

theorem eq_updates_of_mem_next {i} (h : εClosure σ nfa wf pos matched next stack = (matched', next'))
  (mem' : i ∈ next.states) :
  next'.updates[i] = next.updates[i] := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next =>
    simp [εClosure.base] at h
    simp [h]
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    exact ih h mem'
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    have ih : next'.updates[i] = updates'[i] := ih h (SparseSet.mem_insert_of_mem mem mem')
    simp [ih, updates']
    split
    next =>
      simp [Vector.getElem_set]
      intro eq
      exact (mem (Fin.eq_of_val_eq eq ▸ mem')).elim
    next => rfl

theorem eq_matched_some (h : εClosure σ nfa wf pos matched next stack = (matched', next'))
  (isSome : matched.isSome) :
  matched' = matched := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next =>
    simp [εClosure.base] at h
    simp [h]
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    exact ih h isSome
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    have eq : matched' = matched := by
      simp [matched']
      match matched with
      | some _ => simp
    exact eq ▸ ih h (eq ▸ isSome)

theorem matched_inv (h : εClosure σ nfa wf pos matched next stack = (matched', next'))
  (inv : (isSome : matched.isSome) → ∃ i ∈ next.states, nfa[i] = .done ∧ next.updates[i] = matched.get isSome)
  (isSome' : matched'.isSome) :
  ∃ i ∈ next'.states, nfa[i] = .done ∧ next'.updates[i] = matched'.get isSome' := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next =>
    simp [εClosure.base] at h
    simp_all
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    exact ih h inv
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    have inv' (isSome' : matched'.isSome) : ∃ i ∈ states', nfa[i] = .done ∧ updates'[i] = matched'.get isSome' := by
      match hm : matched with
      | .some update =>
        simp at inv
        have ⟨i, memi, hn, equpdate⟩ := inv
        have eq : updates'[i] = next.updates[i] := by
          simp [updates']
          split
          next =>
            simp [Vector.getElem_set]
            intro eq
            exact (mem (Fin.eq_of_val_eq eq ▸ memi)).elim
          next => rfl
        have eq' : matched' = .some update := by simp [matched', hm]
        exact ⟨i, SparseSet.mem_insert_of_mem mem memi, hn, by simp [eq, eq', equpdate]⟩
      | .none =>
        have : node = .done ∧ matched' = .some update := by
          simp [matched']
          split
          next hn => simp [hn, hm]
          next hn => simp [matched', hn, hm] at isSome'
        exact ⟨state, SparseSet.mem_insert mem, this.1, by simp [updates', writeUpdate, this]⟩
    exact ih h inv'

theorem not_done_of_none (result) (h : εClosure σ nfa wf pos matched next stack = result)
  (isNone : result.1 = .none)
  (inv : next.NotDoneInv σ nfa) :
  result.2.NotDoneInv σ nfa := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next =>
    simp [εClosure.base] at h
    simpa [←h] using inv
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    exact ih h inv
  | not_visited matched next update state stack mem node matched'' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    have inv' : SearchState.NotDoneInv σ nfa ⟨states', updates'⟩ := by
      intro i mem
      simp [states'] at mem
      cases SparseSet.eq_or_mem_of_mem_insert mem with
      | inl eq =>
        rw [eq]
        intro hn
        have isSome'' : matched''.isSome := by
          simp [matched'', node, hn]
        have eq' : result.1 = matched'' := eq_matched_some h isSome''
        simp [eq', matched'', node, hn] at isNone
      | inr mem => exact inv i mem
    exact ih h inv'

def LowerInvStep (pos : Pos s) (states : SparseSet nfa.nodes.size) (stack : εStack σ nfa) : Prop :=
  ∀ i j update, i ∈ states → nfa.εStep' pos i j update → j ∈ states ∨ ∃ update', (update', j) ∈ stack

def LowerBoundStep (pos : Pos s) (states : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j update, i ∈ states → nfa.εStep' pos i j update → j ∈ states

def LowerBound (pos : Pos s) (states : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j update, i ∈ states → nfa.εClosure' pos i j update → j ∈ states

theorem LowerBound.of_empty {pos : Pos s} {states : SparseSet nfa.nodes.size} (h : states.isEmpty) :
  LowerBound pos states := by
  intro i j update mem cls
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

theorem LowerBound.of_step {pos : Pos s} {states : SparseSet nfa.nodes.size} (h : LowerBoundStep pos states) :
  εClosure.LowerBound pos states := by
  intro i j update mem cls
  induction cls with
  | base => exact mem
  | step step _ ih => exact ih (h _ _ _ mem step)

namespace LowerInvStep

variable {states : SparseSet nfa.nodes.size} {entry : σ.Update × Fin nfa.nodes.size}

theorem preserves' {stack' : εStack σ nfa} (hmem : entry.2 ∉ states) (nextEntries) (hstack : stack' = nextEntries ++ stack)
  (h : ∀ j update, nfa.εStep' pos entry.2 j update → ∃ update', (update', j) ∈ nextEntries)
  (inv : LowerInvStep pos states (entry :: stack)) :
  LowerInvStep pos (states.insert entry.2 hmem) stack' := by
  intro i j update mem step
  cases SparseSet.eq_or_mem_of_mem_insert mem with
  | inl eq =>
    have ⟨update', mem'⟩ := h j update (eq ▸ step)
    exact .inr ⟨update', by simp [hstack, mem']⟩
  | inr mem =>
    match inv i j update mem step with
    | .inl mem => exact .inl (SparseSet.mem_insert_of_mem hmem mem)
    | .inr ⟨update', mem'⟩ =>
      simp at mem'
      cases mem' with
      | inl eq => exact .inl (eq ▸ SparseSet.mem_insert hmem)
      | inr mem' => exact .inr ⟨update', by simp [hstack, mem']⟩

theorem preserves (wf : nfa.WellFormed) (hmem : entry.2 ∉ states) (inv : LowerInvStep pos states (entry :: stack)) :
  LowerInvStep pos (states.insert entry.2 hmem) (pushNext σ nfa pos nfa[entry.2] (wf.inBounds entry.2) entry.1 stack) := by
  cases hn : nfa[entry.2], wf.inBounds entry.2, entry.1, stack using pushNext.fun_cases' σ nfa pos with
  | epsilon _ _ state' inBounds =>
    rename_i update
    simp [pushNext.epsilon rfl]
    apply inv.preserves' hmem [(update, ⟨state', inBounds⟩)] (by simp)
    simp
    intro j update' step
    simp [εStep'.epsilon hn] at step
    simp [Fin.ext_iff, step]
  | split _ _ state₁ state₂ inBounds =>
    rename_i update
    simp [pushNext.split rfl]
    apply inv.preserves' hmem [(update, ⟨state₁, inBounds.1⟩), (update, ⟨state₂, inBounds.2⟩)] (by simp)
    simp [←and_or_left]
    intro j update' step
    simp [εStep'.split hn] at step
    simp [Fin.ext_iff, step]
  | save _ _ offset state' inBounds =>
    rename_i update
    simp [pushNext.save rfl]
    apply inv.preserves' hmem [(σ.write update offset pos, ⟨state', inBounds⟩)] (by simp)
    simp
    intro j update' step
    simp [εStep'.save hn] at step
    simp [Fin.ext_iff, step]
  | anchor_pos _ _ anchor state' inBounds ht =>
    rename_i update
    simp [pushNext.anchor_pos rfl ht]
    apply inv.preserves' hmem [(update, ⟨state', inBounds⟩)] (by simp)
    simp
    intro j update' step
    simp [εStep'.anchor hn] at step
    simp [Fin.ext_iff, step]
  | anchor_neg _ _ anchor state' inBounds ht =>
    simp [pushNext.anchor_neg rfl ht]
    apply inv.preserves' hmem [] (by simp)
    simp
    intro j update' step
    simp [εStep'.anchor hn, ht] at step
  | done _ _ inBounds =>
    simp [pushNext.done rfl]
    apply inv.preserves' hmem [] (by simp)
    simp
    intro j update' step
    simp [εStep'.done hn] at step
  | fail _ _ inBounds =>
    simp [pushNext.fail rfl]
    apply inv.preserves' hmem [] (by simp)
    simp
    intro j update' step
    simp [εStep'.fail hn] at step
  | char _ _ c state' inBounds =>
    simp [pushNext.char rfl]
    apply inv.preserves' hmem [] (by simp)
    simp
    intro j update' step
    simp [εStep'.char hn] at step
  | sparse _ _ cs state' inBounds =>
    simp [pushNext.sparse rfl]
    apply inv.preserves' hmem [] (by simp)
    simp
    intro j update' step
    simp [εStep'.sparse hn] at step

end LowerInvStep

theorem lower_bound_step {pos : Pos s} (h : εClosure σ nfa wf pos matched next stack = (matched', next'))
  (inv : LowerInvStep pos next.states stack) :
  LowerBoundStep pos next'.states := by
  induction matched, next, stack using εClosure.induct' σ nfa wf pos with
  | base matched next =>
    simp_all [εClosure.base]
    intro i j update mem step
    simpa using inv i j update mem step
  | visited matched next update state stack mem ih =>
    simp [εClosure.visited mem] at h
    have inv' : LowerInvStep pos next.states stack := by
      intro i j update mem' step'
      have := inv i j update mem' step'
      match this with
      | .inl mem => exact .inl mem
      | .inr ⟨update', mem''⟩ =>
        simp at mem''
        cases mem'' with
        | inl h => exact .inl (h.2 ▸ mem)
        | inr h => exact .inr ⟨update', h⟩
    exact ih h inv'
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    exact ih h (inv.preserves wf mem)

theorem lower_bound {i update} (h : εClosure σ nfa wf pos matched next [(update, i)] = (matched', next'))
  (lb : LowerBound pos next.states) :
  LowerBound pos next'.states := by
  have inv : LowerInvStep pos next.states [(update, i)] := by
    intro i j update mem step
    exact .inl (lb _ _ _ mem (NFA.εClosure'.single step) )
  have lb_step := εClosure.lower_bound_step h inv
  exact LowerBound.of_step lb_step

end

-- Theorems that hold for HistoryStrategy
section

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {pos : Pos s}
  {matched : Option (List (Nat × Pos s))} {next : SearchState (HistoryStrategy s) nfa} {stack : εStack (HistoryStrategy s) nfa}
  {matched' : Option (List (Nat × Pos s))} {next' : SearchState (HistoryStrategy s) nfa}

/--
Intuition: given that we reached `i₀` (from `nfa.start`) with `pos₀` and `update₀`, the εClosure
traversal first puts states reachable from `i₀` into the stack with an appropriate update list.
Next, the traversal pops the states from the stack and writes them to `next`, recording the update
list to `updates` for the necessary states. Since we only care about ε-transitions, the position
doesn't change during the traversal.

At the end of the traversal, we can guarantee that all states in `next` were already in `states₀` or
they are reachable from `i₀` with the updates written to `next.updates`.
-/
structure UpperInv (states₀ : SparseSet nfa.nodes.size) (pos₀ : Pos s) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos s))
  (next : SearchState (HistoryStrategy s) nfa) (stack : εStack (HistoryStrategy s) nfa) : Prop where
  -- The intuition is that `update₀` corresponds to the update list from `nfa.start` to `i₀`, and
  -- `update'` is the update list from `i₀` to `j`. Therefore, `update₀ ++ update'` gives the update
  -- list from `nfa.start` to `j`.
  mem_stack : ∀ update j, (update, j) ∈ stack →
    ∃ update', update = update₀ ++ update' ∧ nfa.εClosure' pos₀ i₀ j update'
  mem_next : ∀ j ∈ next.states,
    j ∈ states₀ ∨ ∃ update', nfa.εClosure' pos₀ i₀ j update' ∧ (writeUpdate nfa[j] → next.updates[j] = update₀ ++ update')

namespace UpperInv

variable {states₀ : SparseSet nfa.nodes.size} {pos₀ : Pos s} {i₀ : Fin nfa.nodes.size} {update₀ : List (Nat × Pos s)}
  {next : SearchState (HistoryStrategy s) nfa} {entry : List (Nat × Pos s) × Fin nfa.nodes.size} {stack : εStack (HistoryStrategy s) nfa}

theorem preserves' {stack'} {node} (hn : nfa[entry.2] = node) (nextEntries) (hstack : stack' = nextEntries ++ stack)
  (not_mem : entry.2 ∉ next.states)
  (h : ∀ update j, (update, j) ∈ nextEntries → ∃ update', update = entry.1 ++ List.ofOption update' ∧ nfa.εStep' pos₀ entry.2 j update')
  (inv : UpperInv states₀ pos₀ i₀ update₀ next (entry :: stack)) :
  letI states' := next.states.insert entry.2 not_mem
  letI updates' := if writeUpdate node then next.updates.set entry.2 entry.1 else next.updates
  UpperInv states₀ pos₀ i₀ update₀ ⟨states', updates'⟩ stack' := by
  refine ⟨?mem_stack, ?mem_next⟩
  case mem_stack =>
    intro update j mem
    simp [hstack] at mem
    cases mem with
    | inl mem =>
      have ⟨update', equ, cls⟩ := inv.mem_stack entry.1 entry.2 (by simp)
      have ⟨update'', equ', step⟩ := h update j mem
      have := cls.snoc step
      exact ⟨update' ++ List.ofOption update'', by simp [equ, equ'], cls.snoc step⟩
    | inr mem => exact inv.mem_stack update j (by simp [mem])
  case mem_next =>
    intro j mem
    simp at mem
    cases SparseSet.eq_or_mem_of_mem_insert mem with
    | inl eq =>
      simp [eq]
      have ⟨update', equpdate, cls⟩ := inv.mem_stack entry.1 entry.2 (by simp)
      refine .inr ⟨update', cls, fun write => ?_⟩
      simpa [←hn, write] using equpdate
    | inr mem =>
      match inv.mem_next j mem with
      | .inl mem => exact .inl mem
      | .inr ⟨update', cls, h⟩ =>
        simp
        refine .inr ⟨update', cls, fun write => ?_⟩
        split
        next =>
          have ne : entry.2.val ≠ j.val := Fin.val_ne_of_ne (fun eq => not_mem (eq ▸ mem))
          rw [Vector.getElem_set_ne (h := ne)]
          exact h write
        next => exact h write

theorem preserves {update : List (Nat × Pos s)} {state : Fin nfa.nodes.size} (wf : nfa.WellFormed) (not_mem : state ∉ next.states)
  (inv : UpperInv states₀ pos₀ i₀ update₀ next ((update, state) :: stack)) :
  letI states' := next.states.insert state not_mem
  letI updates' := if writeUpdate nfa[state] then next.updates.set state update else next.updates
  UpperInv states₀ pos₀ i₀ update₀ ⟨states', updates'⟩ (pushNext (HistoryStrategy s) nfa pos₀ nfa[state] (wf.inBounds state) update stack) := by
  cases hn : nfa[state], wf.inBounds state, update, stack using pushNext.fun_cases' (HistoryStrategy s) nfa pos₀ with
  | epsilon update state state' inBounds =>
    simp [pushNext.epsilon rfl]
    -- Lean slows down when deciding which term to unify with `entry`.
    apply inv.preserves' (entry := (update, state)) hn [(update, ⟨state', inBounds⟩)] (by simp) not_mem
    simp [HistoryStrategy, εStep'.epsilon hn]
  | split update state state₁ state₂ inBounds =>
    simp [pushNext.split rfl]
    apply inv.preserves' (entry := (update, state)) hn [(update, ⟨state₁, inBounds.1⟩), (update, ⟨state₂, inBounds.2⟩)] (by simp) not_mem
    simp [HistoryStrategy, ←and_or_left, εStep'.split hn]
    rw [forall_swap]
    simp
  | save update state offset state' inBounds =>
    simp [pushNext.save rfl]
    apply inv.preserves' (entry := (update, state)) hn [((HistoryStrategy s).write update offset pos₀, ⟨state', inBounds⟩)] (by simp) not_mem
    simp [HistoryStrategy, εStep'.save hn]
  | anchor_pos update state anchor state' inBounds ht =>
    simp [pushNext.anchor_pos rfl ht]
    apply inv.preserves' (entry := (update, state)) hn [(update, ⟨state', inBounds⟩)] (by simp) not_mem
    simp [HistoryStrategy, εStep'.anchor hn, ht]
  | anchor_neg update state anchor state' inBounds ht =>
    simp [pushNext.anchor_neg rfl ht]
    exact inv.preserves' (entry := (update, state)) hn [] (by simp) not_mem (by simp)
  | done update state inBounds =>
    simp [pushNext.done rfl]
    exact inv.preserves' (entry := (update, state)) hn [] (by simp) not_mem (by simp)
  | fail update state inBounds =>
    simp [pushNext.fail rfl]
    exact inv.preserves' (entry := (update, state)) hn [] (by simp) not_mem (by simp)
  | char update state c state' inBounds =>
    simp [pushNext.char (node := .char c state') rfl]
    exact inv.preserves' (entry := (update, state)) hn [] (by simp) not_mem (by simp)
  | sparse update state cs state' inBounds =>
    simp [pushNext.sparse (node := .sparse cs state') rfl]
    exact inv.preserves' (entry := (update, state)) hn [] (by simp) not_mem (by simp)

end UpperInv

/--
All new states in `next'` are reachable from the starting state `i₀` and have corresponding updates in `next'.updates`.
-/
theorem upper_boundAux (states₀ : SparseSet nfa.nodes.size) (pos₀ : Pos s) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos s))
  (h : εClosure (HistoryStrategy s) nfa wf pos₀ matched next stack = (matched', next'))
  (inv₀ : UpperInv states₀ pos₀ i₀ update₀ next stack) :
  UpperInv states₀ pos₀ i₀ update₀ next' []  := by
  induction matched, next, stack using εClosure.induct' (HistoryStrategy s) nfa wf pos₀ with
  | base matched next =>
    simp [↓εClosure.base] at h
    simp [h] at inv₀
    exact inv₀
  | visited matched next update state stack mem ih =>
    rw [εClosure.visited mem] at h
    have inv' : εClosure.UpperInv states₀ pos₀ i₀ update₀ next stack := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        exact inv₀.mem_next j mem
    exact ih h inv'
  | not_visited matched next update state stack mem node matched' states' updates' ih =>
    rw [εClosure.not_visited mem] at h
    exact ih h (inv₀.preserves wf mem)

/--
Upper invariant at the start of the εClosure traversal.
-/
theorem UpperInv.intro {i₀ update₀} (pos₀ : Pos s) :
  εClosure.UpperInv next.states pos₀ i₀ update₀ next [(update₀, i₀)] := by
  refine ⟨?mem_stack, ?mem_next⟩
  case mem_stack =>
    simp [HistoryStrategy]
    exact .base
  case mem_next =>
    intro j mem
    exact .inl mem

theorem upper_bound {i} {update : List (Nat × Pos s)}
  (h : εClosure (HistoryStrategy s) nfa wf pos matched next [(update, i)] = (matched', next')) :
  ∀ j ∈ next'.states, j ∈ next.states ∨
    ∃ update', nfa.εClosure' pos i j update' ∧ (writeUpdate nfa[j] → next'.updates[j] = update ++ update') := by
  have := εClosure.upper_boundAux next.states pos i update h (UpperInv.intro pos)
  exact this.mem_next

/--
`εClosure` inserts all states in the ε-closure of `i` into `next.states`.
-/
theorem mem_next {i update}
  (h : εClosure (HistoryStrategy s) nfa wf pos matched next [(update, i)] = (matched', next'))
  (lb : LowerBound pos next.states)
  {j update'} (cls : nfa.εClosure' pos i j update') :
  j ∈ next'.states := by
  have : i ∈ next'.states := εClosure.mem_next_of_mem_stack (entry := (update, i)) h (by simp)
  exact εClosure.lower_bound h lb i j update' this cls

/--
All states in `next'.states` are already in `next.states` or they are reachable from `i` with the
updates written to `next'.updates`.
-/
theorem write_updates_of_mem_next {i j} {update : List (Nat × Pos s)}
  (h : εClosure (HistoryStrategy s) nfa wf pos matched next [(update, i)] = (matched', next')) (mem : j ∈ next'.states) :
  j ∈ next.states ∨ ∃ update', nfa.εClosure' pos i j update' ∧ (writeUpdate nfa[j] → next'.updates[j] = update ++ update') :=
  εClosure.upper_bound h j mem

/--
For all states in the ε-closure of `i`, it's already in `next.states` or there is a path from `i`
whose updates are written to `next.updates`. The written update list can be different since the
traversal may have reached the state through a different path.
-/
theorem write_updates {i j} {update update' : List (Nat × Pos s)}
  (h : εClosure (HistoryStrategy s) nfa wf pos matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound pos next.states) (cls : nfa.εClosure' pos i j update') :
  j ∈ next.states ∨ ∃ update', nfa.εClosure' pos i j update' ∧ (writeUpdate nfa[j] → next'.updates[j] = update ++ update') :=
  εClosure.write_updates_of_mem_next h (mem_next h lb cls)

theorem inv_of_inv {pos₀} (h : εClosure (HistoryStrategy s) nfa wf pos matched next [([], ⟨nfa.start, wf.start_lt⟩)] = (matched', next'))
  (le : pos₀ ≤ pos) (inv : next.Inv nfa wf pos₀ pos) :
  next'.Inv nfa wf pos₀ pos := by
  intro i mem
  have := εClosure.write_updates_of_mem_next h mem
  match this with
  | .inl mem =>
    have equ := εClosure.eq_updates_of_mem_next h mem
    exact equ ▸ inv i mem
  | .inr ⟨update, cls, write⟩ =>
    simp at write
    exact ⟨update, .init le cls, write⟩

end

end Regex.VM.εClosure
