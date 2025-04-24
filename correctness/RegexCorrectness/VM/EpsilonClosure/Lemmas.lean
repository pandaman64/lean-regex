import RegexCorrectness.Data.SparseSet
import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure.Basic

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.NFA (εStep')
open String (Pos Iterator)

namespace Regex.VM

-- Theorems that hold for any strategy
section

variable {σ : Strategy} {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {matched : Option σ.Update} {next : SearchState σ nfa} {stack : εStack σ nfa}
  {matched' : Option σ.Update} {next' : SearchState σ nfa}

theorem εClosure.subset (h : εClosure σ nfa wf it matched next stack = (matched', next')) :
  next.states ⊆ next'.states := by
  induction matched, next, stack using εClosure.induct' σ nfa wf it with
  | base matched next =>
    simp [εClosure_base] at h
    simp [h]
    exact SparseSet.subset_self
  | visited matched next update state stack mem ih =>
    rw [εClosure_visited mem] at h
    exact ih h
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure_epsilon mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | anchor_pos matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | anchor_neg matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure_split mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure_save mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure_done mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure_char mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure_sparse mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure_fail mem hn] at h
    exact (SparseSet.subset_trans SparseSet.subset_insert (ih h))

theorem εClosure.mem_next_of_mem_stack {i update} (h : εClosure σ nfa wf it matched next stack = (matched', next'))
  (mem_stack : (update, i) ∈ stack) :
  i ∈ next'.states := by
  induction matched, next, stack using εClosure.induct' σ nfa wf it with
  | base matched next => simp at mem_stack
  | visited matched next update state stack mem ih =>
    rw [εClosure_visited mem] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset mem this
    | .inr mem => exact ih h mem
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure_epsilon mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h (by simp [mem])
  | anchor_pos matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h (by simp [mem])
  | anchor_neg matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h (by simp [mem])
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure_split mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h (by simp [mem])
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure_save mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h (by simp [mem])
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure_done mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h mem
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure_char mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h mem
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure_sparse mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h mem
  | fail matched next update state stack' mem hn next'' ih =>
    rw [εClosure_fail mem hn] at h
    simp at mem_stack
    match mem_stack with
    | .inl ⟨_, eq⟩ =>
      subst i
      have : next''.states ⊆ next'.states := εClosure.subset h
      exact SparseSet.mem_of_mem_of_subset SparseSet.mem_insert this
    | .inr mem => exact ih h mem

theorem εClosure.eq_updates_of_mem_next {i} (h : εClosure σ nfa wf it matched next stack = (matched', next'))
  (mem' : i ∈ next.states) :
  next'.updates[i] = next.updates[i] := by
  induction matched, next, stack using εClosure.induct' σ nfa wf it with
  | base matched next =>
    simp [εClosure_base] at h
    simp [h]
  | visited matched next update state stack mem ih =>
    rw [εClosure_visited mem] at h
    exact ih h mem'
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure_epsilon mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | anchor_pos matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | anchor_neg matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure_split mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure_save mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure_done mem hn] at h
    have ne : state.val ≠ i.val := by
      intro eq
      exact absurd (Fin.eq_of_val_eq eq ▸ mem') mem
    have := ih h (SparseSet.mem_insert_of_mem mem')
    simp [next', ne] at this
    simp [this]
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure_char mem hn] at h
    have ne : state.val ≠ i.val := by
      intro eq
      exact absurd (Fin.eq_of_val_eq eq ▸ mem') mem
    have := ih h (SparseSet.mem_insert_of_mem mem')
    simp [next', ne] at this
    simp [this]
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure_sparse mem hn] at h
    have ne : state.val ≠ i.val := by
      intro eq
      exact absurd (Fin.eq_of_val_eq eq ▸ mem') mem
    have := ih h (SparseSet.mem_insert_of_mem mem')
    simp [next', ne] at this
    simp [this]
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure_fail mem hn] at h
    exact ih h (SparseSet.mem_insert_of_mem mem')

theorem εClosure.eq_matched_some (h : εClosure σ nfa wf it matched next stack = (matched', next'))
  (isSome : matched.isSome) :
  matched' = matched := by
  induction matched, next, stack using εClosure.induct' σ nfa wf it with
  | base matched next =>
    simp [εClosure_base] at h
    simp [h]
  | visited matched next update state stack mem ih =>
    rw [εClosure_visited mem] at h
    exact ih h isSome
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure_epsilon mem hn] at h
    exact ih h isSome
  | anchor_pos matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    exact ih h isSome
  | anchor_neg matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    exact ih h isSome
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure_split mem hn] at h
    exact ih h isSome
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure_save mem hn] at h
    exact ih h isSome
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure_done mem hn] at h
    have : (matched <|> .some update) = matched := by
      cases matched with
      | some _ => rfl
      | none => simp at isSome
    simp [this] at ih h
    exact ih h isSome
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure_char mem hn] at h
    exact ih h isSome
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure_sparse mem hn] at h
    exact ih h isSome
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure_fail mem hn] at h
    exact ih h isSome

theorem εClosure.matched_inv (h : εClosure σ nfa wf it matched next stack = (matched', next'))
  (inv : (isSome : matched.isSome) → ∃ i ∈ next.states, nfa[i] = .done ∧ next.updates[i] = matched.get isSome)
  (isSome' : matched'.isSome) :
  ∃ i ∈ next'.states, nfa[i] = .done ∧ next'.updates[i] = matched'.get isSome' := by
  induction matched, next, stack using εClosure.induct' σ nfa wf it with
  | base matched next =>
    simp [εClosure_base] at h
    simp_all
  | visited matched next update state stack mem ih =>
    rw [εClosure_visited mem] at h
    exact ih h inv
  | epsilon matched next update state stack' state' mem hn next'' ih =>
    rw [εClosure_epsilon mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | anchor_pos matched next update state stack' anchor state' mem hn next'' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | anchor_neg matched next update state stack' anchor state' mem hn next'' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | split matched next update state stack' state₁ state₂ mem hn next'' ih =>
    rw [εClosure_split mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | save matched next update state stack' offset state' mem hn next'' ih =>
    rw [εClosure_save mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'
  | done matched next update state stack' nmem hn next'' ih =>
    rw [εClosure_done nmem hn] at h
    cases matched with
    | none =>
      simp at h
      have mem'' : state ∈ next.states.insert state := SparseSet.mem_insert
      have := εClosure.subset h
      have mem' : state ∈ next'.states := SparseSet.mem_of_mem_of_subset mem'' this
      have : next'.updates[state] = matched'.get isSome' :=
        calc
          _ = next''.updates[state] := εClosure.eq_updates_of_mem_next h mem''
          _ = update := by simp [next'']
          _ = matched'.get isSome' := by simp [εClosure.eq_matched_some h (by simp)]
      exact ⟨state, mem', hn, this⟩
    | some matched =>
      simp at h inv
      have ⟨i, mem, hdone, eq⟩ := inv
      have mem'' : i ∈ next''.states := SparseSet.mem_insert_of_mem mem
      have := εClosure.subset h
      have mem' : i ∈ next'.states := SparseSet.mem_of_mem_of_subset mem'' this
      have eq₁ : next'.updates[i] = next.updates[i] :=
        calc
          _ = next''.updates[i] := εClosure.eq_updates_of_mem_next h mem''
          _ = next.updates[i] := by
            have : state ≠ i := by
              intro eq
              exact absurd (eq ▸ mem) nmem
            simp [next'', Fin.val_ne_of_ne this]
      have eq₂ : matched' = matched := εClosure.eq_matched_some h (by simp)
      exact ⟨i, mem', hdone, by simp [eq, eq₁, eq₂]⟩
  | char matched next update state stack' c state' mem hn next'' ih =>
    rw [εClosure_char mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      have : next''.updates[i] = next.updates[i] := by
        have : state ≠ i := by
          intro eq
          exact absurd (eq ▸ mem') mem
        simp [next'', Fin.val_ne_of_ne this]
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, this ▸ eq⟩
    exact ih h inv'
  | sparse matched next update state stack' cs state' mem hn next'' ih =>
    rw [εClosure_sparse mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      have : next''.updates[i] = next.updates[i] := by
        have : state ≠ i := by
          intro eq
          exact absurd (eq ▸ mem') mem
        simp [next'', Fin.val_ne_of_ne this]
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, this ▸ eq⟩
    exact ih h inv'
  | fail matched next update state stack' mem hn next'' ih =>
    rw [εClosure_fail mem hn] at h
    have inv' (isSome : matched.isSome) : ∃ i ∈ next''.states, nfa[i] = .done ∧ next''.updates[i] = matched.get isSome := by
      have ⟨i, mem', hdone, eq⟩ := inv isSome
      exact ⟨i, SparseSet.mem_insert_of_mem mem', hdone, eq⟩
    exact ih h inv'

def εClosure.LowerInvStep (it : Iterator) (states : SparseSet nfa.nodes.size) (stack : εStack σ nfa) : Prop :=
  ∀ i j update, i ∈ states → nfa.εStep' it i j update → j ∈ states ∨ ∃ update', (update', j) ∈ stack

def εClosure.LowerBoundStep (it : Iterator) (states : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j update, i ∈ states → nfa.εStep' it i j update → j ∈ states

def εClosure.LowerBound (it : Iterator) (states : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j update, i ∈ states → nfa.εClosure' it i j update → j ∈ states

theorem εClosure.LowerBound.of_step {it : Iterator} {states : SparseSet nfa.nodes.size} (h : εClosure.LowerBoundStep it states) :
  εClosure.LowerBound it states := by
  intro i j update mem cls
  induction cls with
  | base => exact mem
  | step step _ ih => exact ih (h _ _ _ mem step)

theorem εClosure.lower_bound_step {it : Iterator} (h : εClosure σ nfa wf it matched next stack = (matched', next'))
  (inv : εClosure.LowerInvStep it next.states stack) :
  εClosure.LowerBoundStep it next'.states := by
  induction matched, next, stack using εClosure.induct' σ nfa wf it with
  | base matched next =>
    simp_all
    intro i j update mem step
    simpa using inv i j update mem step
  | visited matched next update state stack mem ih =>
    simp [*] at h
    have inv' : εClosure.LowerInvStep it next.states stack := by
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
  | epsilon matched next update state stack' state' mem hn next' ih =>
    rw [εClosure_epsilon mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) ((update, state') :: stack') := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.epsilon hn] at step'
        exact .inr ⟨update, by simp [step']⟩
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | anchor_pos matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) ((update, state') :: stack') := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.anchor hn] at step'
        exact .inr ⟨update, by simp [step']⟩
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | anchor_neg matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) stack' := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.anchor hn, ] at step'
        simp [step'] at test
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure_split mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) ((update, state₁) :: (update, state₂) :: stack') := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.split hn] at step'
        cases step'.1 with
        | inl h => exact .inr ⟨update, by simp [h]⟩
        | inr h => exact .inr ⟨update, by simp [h]⟩
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | save matched next update state stack' offset state' mem hn next' ih =>
    rw [εClosure_save mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) ((σ.write update offset it.pos, state') :: stack') := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.save hn] at step'
        exact .inr ⟨σ.write update offset it.pos, by simp [step']⟩
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | done matched next update state stack' mem hn next' ih =>
    rw [εClosure_done mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) stack' := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.done hn] at step'
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure_char mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) stack' := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.char hn] at step'
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure_sparse mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) stack' := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.sparse hn] at step'
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure_fail mem hn] at h
    have inv' : εClosure.LowerInvStep it (next.states.insert state) stack' := by
      intro i j update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq => simp [eq, εStep'.fail hn] at step'
      | inr mem'' =>
        match inv i j update' mem'' step'  with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'

theorem εClosure.lower_bound {i update} (h : εClosure σ nfa wf it matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound it next.states) :
  εClosure.LowerBound it next'.states := by
  have inv : εClosure.LowerInvStep it next.states [(update, i)] := by
    intro i j update mem step
    exact .inl (lb _ _ _ mem (NFA.εClosure'.single step) )
  have lb_step := εClosure.lower_bound_step h inv
  exact εClosure.LowerBound.of_step lb_step

end

-- Theorems that hold for HistoryStrategy
section

variable {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {matched : Option (List (Nat × Pos))} {next : SearchState HistoryStrategy nfa} {stack : εStack HistoryStrategy nfa}
  {matched' : Option (List (Nat × Pos))} {next' : SearchState HistoryStrategy nfa}

/--
Intuition: given that we reached `i₀` (from `nfa.start`) with `it₀` and `update₀`, the εClosure
traversal first puts states reachable from `i₀` into the stack with an appropriate update list.
Next, the traversal pops the states from the stack and writes them to `next`, recording the update
list to `updates` for the necessary states. Since we only care about ε-transitions, the iterator
doesn't change during the traversal.

At the end of the traversal, we can guarantee that all states in `next` were already in `states₀` or
they are reachable from `i₀` with the updates written to `next.updates`.
-/
structure εClosure.UpperInv (states₀ : SparseSet nfa.nodes.size) (it₀ : Iterator) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos))
  (next : SearchState HistoryStrategy nfa) (stack : εStack HistoryStrategy nfa) : Prop where
  -- The intuition is that `update₀` corresponds to the update list from `nfa.start` to `i₀`, and
  -- `update'` is the update list from `i₀` to `j`. Therefore, `update₀ ++ update'` gives the update
  -- list from `nfa.start` to `j`.
  mem_stack : ∀ update j, (update, j) ∈ stack →
    ∃ update', update = update₀ ++ update' ∧ nfa.εClosure' it₀ i₀ j update'
  mem_next : ∀ j ∈ next.states,
    j ∈ states₀ ∨ ∃ update', nfa.εClosure' it₀ i₀ j update' ∧ (WriteUpdate j → next.updates[j] = update₀ ++ update')

/--
All new states in `next'` are reachable from the starting state `i₀` and have corresponding updates in `next'.updates`.
-/
theorem εClosure.upper_boundAux (states₀ : SparseSet nfa.nodes.size) (it₀ : Iterator) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos))
  (h : εClosure HistoryStrategy nfa wf it₀ matched next stack = (matched', next'))
  (v : it₀.Valid)
  (inv₀ : εClosure.UpperInv states₀ it₀ i₀ update₀ next stack) :
  εClosure.UpperInv states₀ it₀ i₀ update₀ next' []  := by
  induction matched, next, stack using εClosure.induct' HistoryStrategy nfa wf it₀ with
  | base matched next =>
    simp [εClosure_base] at h
    simp [h] at inv₀
    exact inv₀
  | visited matched next update state stack mem ih =>
    rw [εClosure_visited mem] at h
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ next stack := by
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
    rw [εClosure_epsilon mem hn] at h
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update, state') :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' it₀ state state' .none := by
            simp [εStep'.epsilon hn, v]
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
  | anchor_pos matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_pos mem hn test] at h
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update, state') :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' it₀ state state' .none := by
            simp [εStep'.anchor hn, v, test]
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
  | anchor_neg matched next update state stack' anchor state' mem hn next' test ih =>
    rw [εClosure_anchor_neg mem hn test] at h
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ stack' := by
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
  | split matched next update state stack' state₁ state₂ mem hn next' ih =>
    rw [εClosure_split mem hn] at h
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update, state₁) :: (update, state₂) :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' it₀ state state₁ .none := by
            simp [εStep'.split hn, v]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨update', equ, cls'⟩
        | .inr (.inl ⟨equ, eqj⟩) =>
          subst u j
          have step : nfa.εStep' it₀ state state₂ .none := by
            simp [εStep'.split hn, v]
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
    rw [εClosure_save mem hn] at h
    simp [HistoryStrategy] at update matched
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ ((update ++ [(offset, it₀.pos)], state') :: stack') := by
      have ⟨update', equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ', eqj⟩ =>
          subst u j
          have last : nfa.εStep' it₀ state state' (.some (offset, it₀.pos)) :=
            NFA.Step.save (Nat.zero_le _) state.isLt hn v
          have := cls.snoc last
          exact ⟨update' ++ [(offset, it₀.pos)], by simp [equ]; apply List.append_assoc, this⟩
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
    rw [εClosure_done mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | char matched next update state stack' c state' mem hn next' ih =>
    rw [εClosure_char mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | sparse matched next update state stack' cs state' mem hn next' ih =>
    rw [εClosure_sparse mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | fail matched next update state stack' mem hn next' ih =>
    rw [εClosure_fail mem hn] at h
    have inv' : εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates⟩ stack' := by
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
    (inv₀ : εClosure.UpperInv states₀ it₀ i₀ update₀ next ((update, state) :: stack')) :
    εClosure.UpperInv states₀ it₀ i₀ update₀ ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
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
theorem εClosure.UpperInv.intro {i₀ update₀} (it₀ : Iterator) (v : it₀.Valid) :
  εClosure.UpperInv next.states it₀ i₀ update₀ next [(update₀, i₀)] := by
  refine ⟨?mem_stack, ?mem_next⟩
  case mem_stack =>
    simp [HistoryStrategy]
    exact .base v
  case mem_next =>
    intro j mem
    exact .inl mem

theorem εClosure.upper_bound {i} {update : List (Nat × Pos)}
  (h : εClosure HistoryStrategy nfa wf it matched next [(update, i)] = (matched', next'))
  (v : it.Valid) :
  ∀ j ∈ next'.states, j ∈ next.states ∨
    ∃ update', nfa.εClosure' it i j update' ∧ (WriteUpdate j → next'.updates[j] = update ++ update') := by
  have := εClosure.upper_boundAux next.states it i update h v (εClosure.UpperInv.intro it v)
  exact this.mem_next

/--
`εClosure` inserts all states in the ε-closure of `i` into `next.states`.
-/
theorem mem_next_of_εClosure {i update}
  (h : εClosure HistoryStrategy nfa wf it matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound it next.states)
  {j update'} (cls : nfa.εClosure' it i j update') :
  j ∈ next'.states := by
  have : i ∈ next'.states := εClosure.mem_next_of_mem_stack (update := update) h (by simp)
  exact εClosure.lower_bound h lb i j update' this cls

/--
All states in `next'.states` are already in `next.states` or they are reachable from `i` with the
updates written to `next'.updates`.
-/
theorem εClosure.write_updates_of_mem_next {i j} {update : List (Nat × Pos)}
  (h : εClosure HistoryStrategy nfa wf it matched next [(update, i)] = (matched', next'))
  (v : it.Valid) (mem : j ∈ next'.states) :
  j ∈ next.states ∨ ∃ update', nfa.εClosure' it i j update' ∧ (WriteUpdate j → next'.updates[j] = update ++ update') :=
  εClosure.upper_bound h v j mem

/--
For all states in the ε-closure of `i`, it's already in `next.states` or there is a path from `i`
whose updates are written to `next.updates`. The written update list can be different since the
traversal may have reached the state through a different path.
-/
theorem write_updates_of_εClosure {i j} {update update' : List (Nat × Pos)} (v : it.Valid)
  (h : εClosure HistoryStrategy nfa wf it matched next [(update, i)] = (matched', next'))
  (lb : εClosure.LowerBound it next.states) (cls : nfa.εClosure' it i j update') :
  j ∈ next.states ∨ ∃ update', nfa.εClosure' it i j update' ∧ (WriteUpdate j → next'.updates[j] = update ++ update') :=
  εClosure.write_updates_of_mem_next h v (mem_next_of_εClosure h lb cls)

theorem εClosure.inv_of_inv (h : εClosure HistoryStrategy nfa wf it matched next [([], ⟨nfa.start, wf.start_lt⟩)] = (matched', next'))
  (v : it.Valid) (inv : next.Inv nfa wf it) :
  next'.Inv nfa wf it := by
  intro i mem
  have := εClosure.write_updates_of_mem_next h v mem
  match this with
  | .inl mem =>
    have equ := εClosure.eq_updates_of_mem_next h mem
    exact equ ▸ inv i mem
  | .inr ⟨update, cls, write⟩ =>
    simp at write
    exact ⟨it, update, .init cls, write⟩

end

end Regex.VM
