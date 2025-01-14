import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep.Basic

set_option autoImplicit false

open Regex.Data (SparseSet Span)
open Regex (NFA)
open Regex.NFA (εStep' εClosure' CharStep)
open String (Pos Iterator)

namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {current : SearchState' nfa} {currentUpdates : Vector (List (Nat × Pos)) nfa.nodes.size}
  {next : SearchState' nfa} {state : Fin nfa.nodes.size}
  {matched' : Option (List (Nat × Pos))} {next' : SearchState' nfa}

theorem stepChar.subset (h : stepChar' nfa wf it currentUpdates next state = (matched', next')) :
  next.states ⊆ next'.states := by
  simp [stepChar'] at h
  split at h
  next c' state' hn =>
    split at h
    next => exact εClosure.subset h
    next => simp_all [SparseSet.subset_self]
  next cs state' =>
    split at h
    next => exact εClosure.subset h
    next => simp_all [SparseSet.subset_self]
  next => simp_all [SparseSet.subset_self]

theorem stepChar.lower_bound (h : stepChar' nfa wf it currentUpdates next state = (matched', next'))
  (lb : εClosure.LowerBound next.states) :
  εClosure.LowerBound next'.states := by
  simp [stepChar'] at h
  split at h
  next c' state' hn =>
    split at h
    next => exact εClosure.lower_bound h lb
    next => simp_all
  next cs state' =>
    split at h
    next => exact εClosure.lower_bound h lb
    next => simp_all
  next => simp_all

theorem stepChar.eq_updates_of_mem_next {i k} (h : stepChar' nfa wf it currentUpdates next i = (matched', next'))
  (mem : k ∈ next.states) :
  next'.updates[k] = next.updates[k] := by
  simp [stepChar'] at h
  split at h
  next c' j hn =>
    split at h
    next => exact εClosure.eq_updates_of_mem_next h mem
    next => simp_all
  next cs j =>
    split at h
    next => exact εClosure.eq_updates_of_mem_next h mem
    next => simp_all
  next => simp_all

theorem stepChar.done_of_matched_some (h : stepChar' nfa wf it currentUpdates next state = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  simp [stepChar'] at h
  split at h
  next c' j hn =>
    split at h
    next => exact εClosure.matched_inv h (by simp) isSome'
    next =>
      simp at h
      simp [←h.1] at isSome'
  next cs j =>
    split at h
    next => exact εClosure.matched_inv h (by simp) isSome'
    next =>
      simp at h
      simp [←h.1] at isSome'
  next =>
    simp at h
    simp [←h.1] at isSome'

theorem mem_next_of_stepChar {l m r i j k update}
  (h : stepChar' nfa wf it currentUpdates next i = (matched', next'))
  (lb : εClosure.LowerBound next.states)
  (step : nfa.CharStep l m it.curr r i j) (cls : nfa.εClosure' ⟨l, it.curr :: m, r⟩ j k update) :
  k ∈ next'.states := by
  simp [stepChar'] at h
  split at h
  next c' j' hn =>
    rw [CharStep.char hn] at step
    simp [←step] at h
    apply mem_next_of_εClosure h lb cls
  next cs j' hn =>
    rw [CharStep.sparse hn] at step
    simp [step.1, ←step.2] at h
    apply mem_next_of_εClosure h lb cls
  next ne₁ ne₂ =>
    have := step.char_or_sparse
    simp_all

theorem stepChar.write_updates_of_mem_next {i k} (span : Span) (hspan : span.iterator = it)
  (h : stepChar' nfa wf it currentUpdates next i = (matched', next'))
  (notEnd : ¬it.atEnd) (mem : k ∈ next'.states) :
  k ∈ next.states ∨ ∃ r' j update',
    span.r = it.curr :: r' ∧
    nfa.CharStep span.l span.m it.curr r' i j ∧
    nfa.εClosure' span.next j k update' ∧
    (WriteUpdate k → next'.updates[k] = currentUpdates.get i ++ update') := by
  simp [stepChar'] at h
  split at h
  next c j hn =>
    split at h
    next eqc =>
      subst it c
      have ⟨r', eqr⟩ := span.exists_cons_of_not_atEnd notEnd
      have := εClosure.write_updates_of_mem_next span.next (span.next_curr_eq_next_pos eqr) h mem
      match this with
      | .inl mem => exact .inl mem
      | .inr ⟨update', cls, write⟩ =>
        have isLt := wf.inBounds' i hn
        exact .inr ⟨r', ⟨j, isLt⟩, update', eqr, NFA.Step.char (Nat.zero_le _) i.isLt hn, cls, write⟩
    next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]
  next cs j hn =>
    split at h
    next cmem =>
      subst it
      have ⟨r', eqr⟩ := span.exists_cons_of_not_atEnd notEnd
      have := εClosure.write_updates_of_mem_next span.next (span.next_curr_eq_next_pos eqr) h mem
      match this with
      | .inl mem => exact .inl mem
      | .inr ⟨update', cls, write⟩ =>
        have isLt := wf.inBounds' i hn
        exact .inr ⟨r', ⟨j, isLt⟩, update', eqr, NFA.Step.sparse (Nat.zero_le _) i.isLt hn cmem, cls, write⟩
    next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]
  next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]

theorem eachStepChar.go.lower_bound {idx hle} (h : eachStepChar'.go nfa wf it current idx hle next = (matched', next'))
  (lb : εClosure.LowerBound next.states) :
  εClosure.LowerBound next'.states := by
  induction idx, hle, next using eachStepChar'.go.induct' nfa wf it current with
  | base next => simp_all
  | found i hlt next matched next'' h' found =>
    rw [eachStepChar'.go_found hlt h' found] at h
    simp_all
    exact stepChar.lower_bound h' lb
  | not_found i hlt next matched next'' h' not_found ih =>
    rw [eachStepChar'.go_not_found hlt h' not_found] at h
    exact ih h (stepChar.lower_bound h' lb)

theorem eachStepChar.go.done_of_matched_some {idx hle} (h : eachStepChar'.go nfa wf it current idx hle next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  induction idx, hle, next using eachStepChar'.go.induct' nfa wf it current with
  | base next =>
    simp at h
    simp [←h.1] at isSome'
  | found i hl next matched next'' h' found =>
    rw [eachStepChar'.go_found hl h' found] at h
    simp at h
    simp [h] at h'
    exact stepChar.done_of_matched_some h' isSome'
  | not_found i hl next matched next'' h' not_found ih =>
    rw [eachStepChar'.go_not_found hl h' not_found] at h
    exact ih h

theorem eachStepChar.done_of_matched_some (h : eachStepChar' nfa wf it current next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome'  :=
  eachStepChar.go.done_of_matched_some h isSome'

theorem eachStepChar.inv_of_stepChar {idx} (hlt : idx < current.states.count)
  (h : stepChar' nfa wf it current.updates next current.states[idx] = (matched', next'))
  (notEnd : ¬it.atEnd)
  (inv_curr : current.Inv nfa wf it)
  (inv_next : next.Inv nfa wf it.next) :
  next'.Inv nfa wf it.next := by
  have ⟨span, update, eqit, path, write⟩ := inv_curr current.states[idx] (SparseSet.mem_get hlt)

  intro k mem
  have := stepChar.write_updates_of_mem_next span eqit h (by simp [notEnd]) mem
  match this with
  | .inl mem =>
    have inv := inv_next k mem
    have equ := stepChar.eq_updates_of_mem_next h mem
    exact equ ▸ inv
  | .inr ⟨r', j, update', eqr, step, cls, write'⟩ =>
    simp [step.write_update] at write
    have write'' : WriteUpdate k → next'.updates[k] = update ++ update' := write ▸ write'
    exact ⟨span.next, update ++ update', by rw [Span.next_iterator eqr, eqit], .more path eqr step cls, write''⟩

theorem eachStepChar.go.inv {idx hle} (h : eachStepChar'.go nfa wf it current idx hle next = (matched', next'))
  (notEnd : ¬it.atEnd)
  (inv_curr : current.Inv nfa wf it)
  (inv_next : next.Inv nfa wf it.next) :
  next'.Inv nfa wf it.next := by
  induction idx, hle, next using eachStepChar'.go.induct' nfa wf it current with
  | base next => simp_all
  | found idx hlt next matched next'' h' found =>
    rw [eachStepChar'.go_found hlt h' found] at h
    simp_all
    exact eachStepChar.inv_of_stepChar hlt h' (by simp [notEnd]) inv_curr inv_next
  | not_found idx hlt next matched next'' h' not_found ih =>
    rw [eachStepChar'.go_not_found hlt h' not_found] at h
    have inv' : next''.Inv nfa wf it.next :=
      eachStepChar.inv_of_stepChar hlt h' (by simp [notEnd]) inv_curr inv_next
    apply ih h inv'

theorem eachStepChar.inv_of_inv {next next'} (h : eachStepChar' nfa wf it current next = (matched', next'))
  (notEnd : ¬it.atEnd) (empty : next.states.isEmpty)
  (inv : current.Inv nfa wf it) :
  next'.Inv nfa wf it.next := by
  simp [eachStepChar'] at h
  exact eachStepChar.go.inv h notEnd inv (.of_empty empty)

end Regex.VM
