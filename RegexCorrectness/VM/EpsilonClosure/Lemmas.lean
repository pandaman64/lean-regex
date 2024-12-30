import RegexCorrectness.Data.SparseSet
import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure.Basic

set_option autoImplicit false

open Regex.Data (SparseSet Vec Span)
open Regex (NFA)
open Regex.NFA (εStep' εClosure')
open String (Pos Iterator)

namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {matched : Option (List (Nat × Pos))} {next : SearchState' nfa} {stack : εStack' nfa}
  {matched' : Option (List (Nat × Pos))} {next' : SearchState' nfa}

theorem εClosure.subset (h : εClosure' nfa wf it matched next stack = (matched', next')) :
  next.states ⊆ next'.states := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next =>
    simp [εClosure'_base] at h
    simp [h]
    exact SparseSet.subset_self
  | visited matched next update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    exact ih h
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure'_epsilon mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure'_split mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure'_save mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure'_done mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure'_char mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure'_sparse mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure'_fail mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))

theorem εClosure.mem_next_of_mem_stack {i update} (h : εClosure' nfa wf it matched next stack = (matched', next'))
  (mem_stack : (update, i) ∈ stack) :
  i ∈ next'.states := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next => simp at mem_stack
  | visited matched next update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset mem (εClosure.subset h)
    | .inr mem => exact ih h mem
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure'_epsilon mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert (εClosure.subset h)
    | .inr mem => exact ih h (by simp [mem])
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure'_split mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert (εClosure.subset h)
    | .inr mem => exact ih h (by simp [mem])
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure'_save mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert (εClosure.subset h)
    | .inr mem => exact ih h (by simp [mem])
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure'_done mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert (εClosure.subset h)
    | .inr mem => exact ih h mem
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure'_char mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert (εClosure.subset h)
    | .inr mem => exact ih h mem
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure'_sparse mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert (εClosure.subset h)
    | .inr mem => exact ih h mem
  | fail matched next update state stack' mem hn next'' ih =>
    rw [εClosure'_fail mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have : next''.states ⊆ next'.states := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h mem

theorem εClosure.eq_updates_of_mem_next {i} (h : εClosure' nfa wf it matched next stack = (matched', next'))
  (mem' : i ∈ next.states) :
  next'.updates[i] = next.updates[i] := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next =>
    simp [εClosure'_base] at h
    simp [h]
  | visited matched next update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    exact ih h mem'
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure'_epsilon mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure'_split mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure'_save mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure'_done mem hn] at h
    have ne : state.val ≠ i.val := by
      intro eq
      exact absurd (Fin.eq_of_val_eq eq ▸ mem') mem
    have := ih h (SparseSet.mem_insert_of_mem mem')
    simp [Vec.get_set_ne next.updates state.isLt i.isLt ne] at this
    simp [this]
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure'_char mem hn] at h
    have ne : state.val ≠ i.val := by
      intro eq
      exact absurd (Fin.eq_of_val_eq eq ▸ mem') mem
    have := ih h (SparseSet.mem_insert_of_mem mem')
    simp [Vec.get_set_ne next.updates state.isLt i.isLt ne] at this
    simp [this]
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure'_sparse mem hn] at h
    have ne : state.val ≠ i.val := by
      intro eq
      exact absurd (Fin.eq_of_val_eq eq ▸ mem') mem
    have := ih h (SparseSet.mem_insert_of_mem mem')
    simp [Vec.get_set_ne next.updates state.isLt i.isLt ne] at this
    simp [this]
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure'_fail mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')

theorem εClosure.eq_matched_some (h : εClosure' nfa wf it matched next stack = (matched', next'))
  (isSome : matched.isSome) :
  matched' = matched := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next =>
    simp [εClosure'_base] at h
    simp [h]
  | visited matched next update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    exact ih h isSome
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure'_epsilon mem hn] at h
    exact ih h isSome
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure'_split mem hn] at h
    exact ih h isSome
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure'_save mem hn] at h
    exact ih h isSome
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure'_done mem hn] at h
    have : (matched <|> .some update) = matched := by
      cases matched with
      | some _ => rfl
      | none => simp at isSome
    simp [this] at ih h
    exact ih h isSome
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure'_char mem hn] at h
    exact ih h isSome
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure'_sparse mem hn] at h
    exact ih h isSome
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure'_fail mem hn] at h
    exact ih h isSome

theorem εClosure.matched_inv (h : εClosure' nfa wf it matched next stack = (matched', next'))
  (inv : (isSome : matched.isSome) → ∃ i ∈ next.states, nfa[i] = .done ∧ next.updates[i] = matched.get isSome)
  (isSome' : matched'.isSome) :
  ∃ i ∈ next'.states, nfa[i] = .done ∧ next'.updates[i] = matched'.get isSome' := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next =>
    simp [εClosure'_base] at h
    simp_all
  | visited matched next update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    exact ih h inv
  | epsilon matched next update state stack' state' mem hn next'' ih =>
    rw [εClosure'_epsilon mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | split matched next update state stack' state₁ state₂ mem hn next'' ih =>
    rw [εClosure'_split mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | save matched next update state stack' offset state' mem hn next'' ih =>
    rw [εClosure'_save mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | done matched next update state stack' nmem hn next'' ih =>
    rw [εClosure'_done nmem hn] at h
    cases matched with
    | none =>
      simp at h
      have mem'' : state ∈ next.states.insert state := SparseSet.mem_insert
      have mem' : state ∈ next'.states := SparseSet.mem_of_mem_of_subset mem'' (εClosure.subset h)
      have : next'.updates[state] = matched'.get isSome' :=
        calc
          _ = next''.updates[state] := εClosure.eq_updates_of_mem_next h mem''
          _ = update := by simp
          _ = matched'.get isSome' := by simp [εClosure.eq_matched_some h (by simp)]
      exact ⟨state, mem', hn, this⟩
    | some matched =>
      simp at h inv
      have ⟨i, mem, hdone, eq⟩ := inv
      have mem'' : i ∈ next''.states := SparseSet.mem_insert_of_mem mem
      have mem' : i ∈ next'.states := SparseSet.mem_of_mem_of_subset mem'' (εClosure.subset h)
      have eq₁ : next'.updates[i] = next.updates[i] :=
        calc
          _ = next''.updates[i] := εClosure.eq_updates_of_mem_next h mem''
          _ = next.updates[i] := by
            simp [next'']
            have : state ≠ i := by
              intro eq
              exact absurd (eq ▸ mem) nmem
            exact Vec.get_set_ne _ _ _ (Fin.val_ne_of_ne this)
      have eq₂ : matched' = matched := εClosure.eq_matched_some h (by simp)
      exact ⟨i, mem', hdone, by simp [eq, eq₁, eq₂]⟩
  | char matched next update state stack' c state' mem hn next'' ih =>
    rw [εClosure'_char mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      have : next''.updates[i] = next.updates[i] := by
        have : state ≠ i := by
          intro eq
          exact absurd (eq ▸ mem') mem
        simp [Vec.get_set_ne next.updates state.isLt i.isLt (Fin.val_ne_of_ne this)]
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, this ▸ eq⟩
    exact ih h inv'
  | sparse matched next update state stack' cs state' mem hn next'' ih =>
    rw [εClosure'_sparse mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      have : next''.updates[i] = next.updates[i] := by
        have : state ≠ i := by
          intro eq
          exact absurd (eq ▸ mem') mem
        simp [Vec.get_set_ne next.updates state.isLt i.isLt (Fin.val_ne_of_ne this)]
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, this ▸ eq⟩
    exact ih h inv'
  | fail matched next update state stack' mem hn next'' ih =>
    rw [εClosure'_fail mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'

def εClosure.LowerInvStep (states : SparseSet nfa.nodes.size) (stack : εStack' nfa) : Prop :=
  ∀ i j span update, i ∈ states → nfa.εStep' span i j update →
    j ∈ states ∨ ∃ update', (update', j) ∈ stack

def εClosure.LowerBoundStep (states : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j span update, i ∈ states → nfa.εStep' span i j update →
    j ∈ states

def εClosure.LowerBound (states : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j span update, i ∈ states → nfa.εClosure' span i j update →
    j ∈ states

theorem εClosure.LowerBound.of_step {states : SparseSet nfa.nodes.size} (h : εClosure.LowerBoundStep states) :
  εClosure.LowerBound states := by
  intro i j span update mem cls
  induction cls with
  | base => exact mem
  | step step _ ih => exact ih (h _ _ _ _ mem step)

theorem εClosure.lower_bound_step (h : εClosure' nfa wf it matched next stack = (matched', next'))
  (inv : εClosure.LowerInvStep next.states stack) :
  εClosure.LowerBoundStep next'.states := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next =>
    simp_all
    intro i j span update mem step
    have := inv i j span update mem step
    simp at this
    exact this
  | visited matched next update state stack mem ih =>
    simp [*] at h
    have inv' : εClosure.LowerInvStep next.states stack := by
      intro i j span update mem' step'
      have := inv i j span update mem' step'
      match this with
      | .inl mem => exact .inl mem
      | .inr ⟨update', mem''⟩ =>
        simp at mem''
        cases mem'' with
        | inl h => exact .inl (h.2 ▸ mem)
        | inr h => exact .inr ⟨update', h⟩
    exact ih h inv'
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure'_epsilon mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) ((update, state') :: stack') := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.epsilon hn] at step'
        exact .inr ⟨update, by simp [step']⟩
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure'_split mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) ((update, state₁) :: (update, state₂) :: stack') := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.split hn] at step'
        cases step'.1 with
        | inl h => exact .inr ⟨update, by simp [h]⟩
        | inr h => exact .inr ⟨update, by simp [h]⟩
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure'_save mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) ((update ++ [(offset, it.pos)], state') :: stack') := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.save hn] at step'
        exact .inr ⟨update ++ [(offset, it.pos)], by simp [step']⟩
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure'_done mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) stack' := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.done hn] at step'
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure'_char mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) stack' := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.char hn] at step'
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure'_sparse mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) stack' := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.sparse hn] at step'
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure'_fail mem hn] at h
    have inv' : εClosure.LowerInvStep (next.states.insert state) stack' := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.fail hn] at step'
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'

theorem εClosure.lower_bound {i update} (h : εClosure' nfa wf it matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound next.states) :
  εClosure.LowerBound next'.states := by
  have inv : εClosure.LowerInvStep next.states [(update, i)] := by
    intro i j span update mem step
    exact .inl (lb _ _ _ _ mem (εClosure'.single step))
  have lb_step := εClosure.lower_bound_step h inv
  exact εClosure.LowerBound.of_step lb_step

/--
Intuition: given that we reached `i₀` (from `nfa.start`) with `span₀` and `update₀`, the εClosure
traversal first puts states reachable from `i₀` into the stack with an appropriate update list.
Next, the traversal pops the states from the stack and writes them to `next`, recording the update
list to `updates` for the necessary states. Since we only care about ε-transitions, span doesn't
change during the traversal.

At the end of the traversal, we can guarantee that all states in `next` were already in `states₀` or
they are reachable from `i₀` with the updates written to `next.updates`.
-/
structure εClosure.UpperInv (states₀ : SparseSet nfa.nodes.size) (span₀ : Span) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos))
  (next : SearchState' nfa) (stack : εStack' nfa) : Prop where
  -- The intuition is that `update₀` corresponds to the update list from `nfa.start` to `i₀`, and
  -- `update'` is the update list from `i₀` to `j`. Therefore, `update₀ ++ update'` gives the update
  -- list from `nfa.start` to `j`.
  mem_stack : ∀ update j, (update, j) ∈ stack →
    ∃ update', update = update₀ ++ update' ∧ nfa.εClosure' span₀ i₀ j update'
  mem_next : ∀ j ∈ next.states,
    j ∈ states₀ ∨ ∃ update', nfa.εClosure' span₀ i₀ j update' ∧ (WriteUpdate j → next.updates[j] = update₀ ++ update')

/--
All new states in `next'` are reachable from the starting state `i₀` and have corresponding updates in `next'.updates`.
-/
theorem εClosure.upper_boundAux (states₀ : SparseSet nfa.nodes.size) (span₀ : Span) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos))
  (eq_curr : span₀.curr = it.pos)
  (h : εClosure' nfa wf it matched next stack = (matched', next'))
  (inv₀ : εClosure.UpperInv states₀ span₀ i₀ update₀ next stack) :
  εClosure.UpperInv states₀ span₀ i₀ update₀ next' []  := by
  induction matched, next, stack using εClosure'.induct' nfa wf it with
  | base matched next =>
    simp [εClosure'_base] at h
    simp [h] at inv₀
    exact inv₀
  | visited matched next update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    have inv' : εClosure.UpperInv states₀ span₀ i₀ update₀ next stack := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        exact inv₀.mem_next j mem
    exact ih h inv'
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure'_epsilon mem hn] at h
    have inv' : εClosure.UpperInv states₀ span₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update, state') :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' span₀ state state' .none := by
            simp [εStep'.epsilon hn]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨update', equ, cls'⟩
        | .inr mem => exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨update', cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure'_split mem hn] at h
    have inv' : εClosure.UpperInv states₀ span₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update, state₁) :: (update, state₂) :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' span₀ state state₁ .none := by
            simp [εStep'.split hn]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨update', equ, cls'⟩
        | .inr (.inl ⟨equ, eqj⟩) =>
          subst u j
          have step : nfa.εStep' span₀ state state₂ .none := by
            simp [εStep'.split hn]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨update', equ, cls'⟩
        | .inr (.inr mem) => exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨update', cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure'_save mem hn] at h
    have inv' : εClosure.UpperInv states₀ span₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update ++ [(offset, it.pos)], state') :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ', eqj⟩ =>
          subst u j
          have last : nfa.εStep' span₀ state state' (.some (offset, span₀.curr)) :=
            NFA.Step.save (Nat.zero_le _) state.isLt hn
          have := cls.snoc last
          exact ⟨update' ++ [(offset, it.pos)], by simp [equ], eq_curr ▸ this⟩
        | .inr mem => exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨update', cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure'_done mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure'_char mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure'_sparse mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure'_fail mem hn] at h
    have inv' : εClosure.UpperInv states₀ span₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ stack' := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨update', cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
where
  inv_done_char_sparse {next state update stack'}
    (inv₀ : εClosure.UpperInv states₀ span₀ i₀ update₀ next ((update, state) :: stack')) :
    εClosure.UpperInv states₀ span₀ i₀ update₀ ⟨next.states.insert state, next.updates.set state state.isLt update⟩ stack' := by
    have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
    refine ⟨?mem_stack, ?mem_next⟩
    case mem_stack =>
      intro u j mem
      exact inv₀.mem_stack u j (by simp [mem])
    case mem_next =>
      intro j mem
      cases SparseSet.eq_or_mem_of_mem_insert mem with
      | inl eq =>
        subst j
        exact .inr ⟨update', cls, by simp [equ]⟩
      | inr mem =>
        match inv₀.mem_next j mem with
        | .inl mem => exact .inl mem
        | .inr ⟨update'', cls', h⟩ =>
          if h' : state = j then
            subst j
            exact .inr ⟨update', cls, by simp [equ]⟩
          else
            have : state.val ≠ j.val := by omega
            exact .inr ⟨update'', cls', by simp [this]; exact h⟩

/--
Upper invariant at the start of the εClosure traversal.
-/
theorem εClosure.UpperInv.intro {i₀ update₀} (span₀ : Span) :
  εClosure.UpperInv next.states span₀ i₀ update₀ next [(update₀, i₀)] := by
  refine ⟨?mem_stack, ?mem_next⟩
  case mem_stack =>
    intro update j mem
    simp at mem
    simp [mem]
    exact .base
  case mem_next =>
    intro j mem
    exact .inl mem

theorem εClosure.upper_bound {i update} (span : Span) (eq_curr : span.curr = it.pos)
  (h : εClosure' nfa wf it matched next [(update, i)] = (matched', next')) :
  ∀ j ∈ next'.states, j ∈ next.states ∨
    ∃ update', nfa.εClosure' span i j update' ∧ (WriteUpdate j → next'.updates[j] = update ++ update') := by
  have := εClosure.upper_boundAux next.states span i update eq_curr h (εClosure.UpperInv.intro span)
  exact this.mem_next

/--
`εClosure'` inserts all states in the ε-closure of `i` into `next.states`.
-/
theorem mem_next_of_εClosure {i update}
  (h : εClosure' nfa wf it matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound next.states)
  {j span update'} (cls : nfa.εClosure' span i j update') :
  j ∈ next'.states := by
  have : i ∈ next'.states := εClosure.mem_next_of_mem_stack (update := update) h (by simp)
  exact εClosure.lower_bound h lb _ _ _ _ this cls

/--
All states in `next'.states` are already in `next.states` or they are reachable from `i` with the
updates written to `next'.updates`.
-/
theorem write_updates_of_mem_next_of_εClosure {i j update} (span : Span) (eq_curr : span.curr = it.pos)
  (h : εClosure' nfa wf it matched next [(update, i)] = (matched', next'))
  (mem : j ∈ next'.states) :
  j ∈ next.states ∨ ∃ update', nfa.εClosure' span i j update' ∧ (WriteUpdate j → next'.updates[j] = update ++ update') :=
  εClosure.upper_bound span eq_curr h j mem

/--
For all states in the ε-closure of `i`, it's already in `next.states` or there is a path from `i`
whose updates are written to `next.updates`. The written update list can be different since the
traversal may have reached the state through a different path.
-/
theorem write_updates_of_εClosure {i j update update'} (span : Span) (eq_curr : span.curr = it.pos)
  (h : εClosure' nfa wf it matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound next.states) (cls : nfa.εClosure' span i j update') :
  j ∈ next.states ∨ ∃ update', nfa.εClosure' span i j update' ∧ (WriteUpdate j → next'.updates[j] = update ++ update') :=
  write_updates_of_mem_next_of_εClosure span eq_curr h (mem_next_of_εClosure h lb cls)

theorem εClosure.inv_of_inv (h : εClosure' nfa wf it matched next [([], ⟨nfa.start, wf.start_lt⟩)] = (matched', next'))
  (v : it.Valid) (inv : next.Inv nfa wf it) :
  next'.Inv nfa wf it := by
  intro i mem
  have ⟨l, r, vf⟩ := v.validFor
  let span : Span := ⟨l.reverse, [], r⟩
  have eqs : span.toString = it.toString := by
    simp [Span.toString, vf.toString]
  have eqp : span.curr = it.pos := by
    simp [Span.curr, vf.pos]
  have eqit : span.iterator = it := by
    simp [Span.iterator, Iterator.ext_iff, eqs, eqp]
  have := write_updates_of_mem_next_of_εClosure span eqp h mem
  match this with
  | .inl mem =>
    have equ := εClosure.eq_updates_of_mem_next h mem
    exact equ ▸ inv i mem
  | .inr ⟨update, cls, write⟩ =>
    simp at write
    exact ⟨span, update, eqit, .init cls, write⟩

end Regex.VM
