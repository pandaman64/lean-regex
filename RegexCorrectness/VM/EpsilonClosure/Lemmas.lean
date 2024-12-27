import RegexCorrectness.Data.SparseSet
import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.VM.EpsilonClosure.Basic
import RegexCorrectness.VM.EpsilonClosure.Path

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open Regex.NFA (εStep' εClosure')
open String (Pos)

namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {pos : Pos}
  {next : SparseSet nfa.nodes.size} {matched : Option (List (Nat × Pos))}
  {updates : Vec (List (Nat × String.Pos)) nfa.nodes.size} {stack : εStack' nfa}
  {next' : SparseSet nfa.nodes.size} {matched' : Option (List (Nat × Pos))}
  {updates' : Vec (List (Nat × String.Pos)) nfa.nodes.size}

def εClosure.LowerInvStep (next : SparseSet nfa.nodes.size) (stack : εStack' nfa) : Prop :=
  ∀ i j span update, i ∈ next → nfa.εStep' span i j update →
    j ∈ next ∨ ∃ update', (update', j) ∈ stack

def εClosure.LowerBoundStep (next : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j span update, i ∈ next → nfa.εStep' span i j update →
    j ∈ next

def εClosure.LowerBound (next : SparseSet nfa.nodes.size) : Prop :=
  ∀ i j span update, i ∈ next → nfa.εClosure' span i j update →
    j ∈ next

theorem εClosure.LowerBound.of_step (h : εClosure.LowerBoundStep next) : εClosure.LowerBound next := by
  intro i j span update mem cls
  induction cls with
  | base => exact mem
  | step step _ ih => exact ih (h _ _ _ _ mem step)

theorem εClosure.lower_bound_step (h : εClosure' nfa wf pos next matched updates stack = (next', matched', updates'))
  (inv : εClosure.LowerInvStep next stack) : εClosure.LowerBoundStep next' := by
  induction next, matched, updates, stack using εClosure'.induct' nfa wf pos with
  | base next matched updates =>
    simp_all
    intro i j span update mem step
    have := inv i j span update mem step
    simp at this
    exact this
  | visited next matched updates update state stack mem ih =>
    simp [*] at h
    have inv' : εClosure.LowerInvStep next stack := by
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
  | epsilon next matched updates update state stack' state' mem hn ih =>
    rw [εClosure'_epsilon mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) ((update, state') :: stack') := by
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
  | split next matched updates update state stack' state₁ state₂ mem hn ih =>
    rw [εClosure'_split mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) ((update, state₁) :: (update, state₂) :: stack') := by
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
  | save next matched updates update state stack' offset state' mem hn ih =>
    rw [εClosure'_save mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) ((update ++ [(offset, pos)], state') :: stack') := by
      intro i j span update' mem' step'
      cases SparseSet.eq_or_mem_of_mem_insert mem' with
      | inl eq =>
        simp [eq, εStep'.save hn] at step'
        exact .inr ⟨update ++ [(offset, pos)], by simp [step']⟩
      | inr mem'' =>
        match inv i j span update' mem'' step' with
        | .inl mem => exact .inl (SparseSet.mem_insert_of_mem mem)
        | .inr ⟨update'', mem'''⟩ =>
          simp at mem'''
          cases mem''' with
          | inl h => exact .inl (h.2 ▸ SparseSet.mem_insert)
          | inr mem => exact .inr ⟨update'', by simp [mem]⟩
    exact ih h inv'
  | done next matched updates update state stack' mem hn ih =>
    rw [εClosure'_done mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) stack' := by
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
  | char next matched updates update state stack' c state' mem hn ih =>
    rw [εClosure'_char mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) stack' := by
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
  | sparse next matched updates update state stack' cs state' mem hn ih =>
    rw [εClosure'_sparse mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) stack' := by
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
  | fail next matched updates update state stack' mem hn ih =>
    rw [εClosure'_fail mem hn] at h
    have inv' : εClosure.LowerInvStep (next.insert state) stack' := by
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

-- TODO: move this to a shared file
/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
def WriteUpdate (i : Fin nfa.nodes.size) : Prop :=
  match nfa[i] with
  | .done | .char _ _ | .sparse _ _ => True
  | _ => False

/--
Intuition: given the starting state `i₀` and the updates `update₀` at `i₀`, the εClosure traversal
first puts states reachable from `i₀` into the stack with an appropriate update list. Next, the
traversal pops the states from the stack and writes them to `next`, recording the update list to
`updates` for the necessary states.

Therefore, at the end of the traversal, we can guarantee that all states in `next` were already in `next₀`
or they are reachable from `i₀` with the updates written to `updates`.
-/
structure εClosure.UpperInv (pos : Pos) (next₀ : SparseSet nfa.nodes.size) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos))
  (next : SparseSet nfa.nodes.size) (updates : Vec (List (Nat × Pos)) nfa.nodes.size) (stack : εStack' nfa) : Prop where
  mem_stack : ∀ update j, (update, j) ∈ stack → ∃ span update', span.curr = pos ∧ update = update₀ ++ update' ∧ nfa.εClosure' span i₀ j update
  mem_next : ∀ j ∈ next, j ∈ next₀ ∨
    ∃ span update', span.curr = pos ∧ nfa.εClosure' span i₀ j (update₀ ++ update') ∧ (WriteUpdate j → updates[j] = update₀ ++ update')

/--
All new states in `next'` are reachable from the starting state `i₀` and have corresponding updates in `updates'`.
-/
theorem εClosure.upper_bound (next₀ : SparseSet nfa.nodes.size) (i₀ : Fin nfa.nodes.size) (update₀ : List (Nat × Pos))
  (h : εClosure' nfa wf pos next matched updates stack = (next', matched', updates'))
  (inv₀ : εClosure.UpperInv pos next₀ i₀ update₀ next updates stack) :
  εClosure.UpperInv pos next₀ i₀ update₀ next' updates' []  := by
  induction next, matched, updates, stack using εClosure'.induct' nfa wf pos with
  | base next matched updates =>
    simp [εClosure'_base] at h
    simp [h] at inv₀
    exact inv₀
  | visited next matched updates update state stack mem ih =>
    rw [εClosure'_visited mem] at h
    have inv' : εClosure.UpperInv pos next₀ i₀ update₀ next updates stack := by
      have ⟨span, update', eqp, equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        exact inv₀.mem_next j mem
    exact ih h inv'
  | epsilon next matched updates update state stack' state' mem hn ih =>
    rw [εClosure'_epsilon mem hn] at h
    have inv' : εClosure.UpperInv pos next₀ i₀ update₀ (next.insert state) updates ((update, state') :: stack') := by
      have ⟨span, update', eqp, equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' span state state' .none := by
            simp [εStep'.epsilon hn]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨span, update', eqp, equ, cls'⟩
        | .inr mem => exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨span, update', eqp, equ ▸ cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
  | split next matched updates update state stack' state₁ state₂ mem hn ih =>
    rw [εClosure'_split mem hn] at h
    have inv' : εClosure.UpperInv pos next₀ i₀ update₀ (next.insert state) updates ((update, state₁) :: (update, state₂) :: stack') := by
      have ⟨span, update', eqp, equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ, eqj⟩ =>
          subst u j
          have step : nfa.εStep' span state state₁ .none := by
            simp [εStep'.split hn]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨span, update', eqp, equ, cls'⟩
        | .inr (.inl ⟨equ, eqj⟩) =>
          subst u j
          have step : nfa.εStep' span state state₂ .none := by
            simp [εStep'.split hn]
          have cls' := cls.snoc step
          simp at cls'
          exact ⟨span, update', eqp, equ, cls'⟩
        | .inr (.inr mem) => exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨span, update', eqp, equ ▸ cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
  | save next matched updates update state stack' offset state' mem hn ih =>
    rw [εClosure'_save mem hn] at h
    have inv' : εClosure.UpperInv pos next₀ i₀ update₀ (next.insert state) updates ((update ++ [(offset, pos)], state') :: stack') := by
      have ⟨span, update', eqp, equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        simp at mem
        match mem with
        | .inl ⟨equ', eqj⟩ =>
          subst u j
          have last : nfa.εStep' span state state' (.some (offset, span.curr)) :=
            NFA.Step.save (Nat.zero_le _) state.isLt hn
          have := eqp ▸ cls.snoc last
          simp at this
          exact ⟨span, update' ++ [(offset, pos)], eqp, by simp [equ], this⟩
        | .inr mem => exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨span, update', eqp, equ ▸ cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
  | done next matched updates update state stack' mem hn ih =>
    rw [εClosure'_done mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | char next matched updates update state stack' c state' mem hn ih =>
    rw [εClosure'_char mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | sparse next matched updates update state stack' cs state' mem hn ih =>
    rw [εClosure'_sparse mem hn] at h
    exact ih h (inv_done_char_sparse inv₀)
  | fail next matched updates update state stack' mem hn ih =>
    rw [εClosure'_fail mem hn] at h
    have inv' : εClosure.UpperInv pos next₀ i₀ update₀ (next.insert state) updates stack' := by
      have ⟨span, update', eqp, equ, cls⟩ := inv₀.mem_stack update state (by simp)
      refine ⟨?mem_stack, ?mem_next⟩
      case mem_stack =>
        intro u j mem
        exact inv₀.mem_stack u j (by simp [mem])
      case mem_next =>
        intro j mem
        cases SparseSet.eq_or_mem_of_mem_insert mem with
        | inl eq =>
          subst j
          exact .inr ⟨span, update', eqp, equ ▸ cls, by simp [WriteUpdate, hn]⟩
        | inr mem => exact inv₀.mem_next j mem
    exact ih h inv'
where
  inv_done_char_sparse {next updates state update stack'}
    (inv₀ : εClosure.UpperInv pos next₀ i₀ update₀ next updates ((update, state) :: stack')) :
    εClosure.UpperInv pos next₀ i₀ update₀ (next.insert state) (updates.set state state.isLt update) stack' := by
    have ⟨span, update', eqp, equ, cls⟩ := inv₀.mem_stack update state (by simp)
    refine ⟨?mem_stack, ?mem_next⟩
    case mem_stack =>
      intro u j mem
      exact inv₀.mem_stack u j (by simp [mem])
    case mem_next =>
      intro j mem
      cases SparseSet.eq_or_mem_of_mem_insert mem with
      | inl eq =>
        subst j
        exact .inr ⟨span, update', eqp, equ ▸ cls, by simp [equ]⟩
      | inr mem =>
        match inv₀.mem_next j mem with
        | .inl mem => exact .inl mem
        | .inr ⟨span', update'', cls', h⟩ =>
          if h' : state = j then
            subst j
            exact .inr ⟨span, update', eqp, equ ▸ cls, by simp [equ]⟩
          else
            have : state.val ≠ j.val := by omega
            exact .inr ⟨span', update'', cls', by simp [this]; exact h⟩

end Regex.VM
