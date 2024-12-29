import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep.Basic
import RegexCorrectness.VM.CharStep.Path
import RegexCorrectness.VM.CharStep.VMPath

set_option autoImplicit false

open Regex.Data (SparseSet Vec Span)
open Regex (NFA)
open Regex.NFA (εStep' εClosure' CharStep)
open String (Pos Iterator)

namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {current : SearchState' nfa} {currentUpdates : Vec (List (Nat × Pos)) nfa.nodes.size}
  {next : SparseSet nfa.nodes.size} {updates : Vec (List (Nat × String.Pos)) nfa.nodes.size}
  {state : Fin nfa.nodes.size}
  {next' : SparseSet nfa.nodes.size} {matched' : Option (List (Nat × Pos))}
  {updates' : Vec (List (Nat × String.Pos)) nfa.nodes.size}

theorem stepChar.lower_bound (h : stepChar' nfa wf it currentUpdates next updates state = (next', matched', updates'))
  (lb : εClosure.LowerBound next) :
  εClosure.LowerBound next' := by
  simp [stepChar'] at h
  split at h
  next c' state' hn =>
    split at h
    next => exact εClosure.lower_bound h lb
    next => simp_all
  next cs state' =>
    split at h
    next eq => exact εClosure.lower_bound h lb
    next => simp_all
  next => simp_all

theorem stepChar.eq_updates_of_mem_next {i k} (h : stepChar' nfa wf it currentUpdates next updates i = (next', matched', updates'))
  (mem : k ∈ next) :
  updates'[k] = updates[k] := by
  simp [stepChar'] at h
  split at h
  next c' j hn =>
    split at h
    next eq => exact εClosure.eq_updates_of_mem_next h mem
    next => simp_all
  next cs j =>
    split at h
    next => exact εClosure.eq_updates_of_mem_next h mem
    next => simp_all
  next => simp_all

theorem mem_next_of_stepChar {l m r i j k update}
  (h : stepChar' nfa wf it currentUpdates next updates i = (next', matched', updates'))
  (lb : εClosure.LowerBound next)
  (step : nfa.CharStep l m it.curr r i j) (cls : nfa.εClosure' ⟨l, it.curr :: m, r⟩ j k update) :
  k ∈ next' := by
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

theorem write_updates_of_mem_next_of_stepChar {i k} (span : Span) (hspan : span.iterator = it)
  (h : stepChar' nfa wf it currentUpdates next updates i = (next', matched', updates'))
  (notEnd : ¬it.atEnd) (mem : k ∈ next') :
  k ∈ next ∨ ∃ r' j update',
    span.r = it.curr :: r' ∧
    nfa.CharStep span.l span.m it.curr r' i j ∧
    nfa.εClosure' span.next j k update' ∧
    (WriteUpdate k → updates'[k] = currentUpdates.get i i.isLt ++ update') := by
  simp [stepChar'] at h
  split at h
  next c j hn =>
    split at h
    next eqc =>
      subst it c
      have ⟨r', eqr⟩ := span.exists_cons_of_not_atEnd notEnd
      have := write_updates_of_mem_next_of_εClosure span.next (span.next_curr_eq_next_pos eqr) h mem
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
      have := write_updates_of_mem_next_of_εClosure span.next (span.next_curr_eq_next_pos eqr) h mem
      match this with
      | .inl mem => exact .inl mem
      | .inr ⟨update', cls, write⟩ =>
        have isLt := wf.inBounds' i hn
        exact .inr ⟨r', ⟨j, isLt⟩, update', eqr, NFA.Step.sparse (Nat.zero_le _) i.isLt hn cmem, cls, write⟩
    next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]
  next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]

theorem eachStepChar.go.lower_bound {i hle} (h : eachStepChar'.go nfa wf it current i hle next updates = (next', matched', updates'))
  (lb : εClosure.LowerBound next) :
  εClosure.LowerBound next' := by
  induction i, hle, next, updates using eachStepChar'.go.induct' nfa wf it current with
  | base next updates => simp_all
  | found i next updates hlt next'' matched updates' h' found =>
    rw [eachStepChar'.go_found hlt h' found] at h
    simp_all
    exact stepChar.lower_bound h' lb
  | not_found i next updates hlt next'' matched updates' h' not_found ih =>
    rw [eachStepChar'.go_not_found hlt h' not_found] at h
    exact ih h (stepChar.lower_bound h' lb)

def eachStepChar.Inv (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (next : SparseSet nfa.nodes.size) (updates : Vec (List (Nat × Pos)) nfa.nodes.size) : Prop :=
  ∀ i ∈ next, ∃ span update, span.iterator = it ∧ nfa.VMPath wf span i update ∧ (WriteUpdate i → updates[i] = update)

theorem eachStepChar.Inv.of_empty (h : next.isEmpty) : eachStepChar.Inv nfa wf it next updates := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

theorem eachStepChar.Inv.of_stepChar {idx} (hlt : idx < current.states.count)
  (h : stepChar' nfa wf it current.updates next updates current.states[idx] = (next', matched', updates'))
  (notEnd : ¬it.atEnd)
  (inv_curr : eachStepChar.Inv nfa wf it current.states current.updates)
  (inv_next : eachStepChar.Inv nfa wf it.next next updates) :
  eachStepChar.Inv nfa wf it.next next' updates' := by
  have ⟨span, update, eqit, path, write⟩ := inv_curr current.states[idx] (SparseSet.mem_get hlt)

  intro k mem
  have := write_updates_of_mem_next_of_stepChar span eqit h (by simp [notEnd]) mem
  match this with
  | .inl mem =>
    have inv := inv_next k mem
    have equ := stepChar.eq_updates_of_mem_next h mem
    exact equ ▸ inv
  | .inr ⟨r', j, update', eqr, step, cls, write'⟩ =>
    simp [step.write_update] at write
    have write'' : WriteUpdate k → updates'[k] = update ++ update' := write ▸ write'
    exact ⟨span.next, update ++ update', by rw [Span.next_iterator eqr, eqit], .more path eqr step cls, write''⟩

theorem eachStepChar.go.inv {idx hle} (h : eachStepChar'.go nfa wf it current idx hle next updates = (next', matched', updates'))
  (notEnd : ¬it.atEnd)
  (inv_curr : eachStepChar.Inv nfa wf it current.states current.updates)
  (inv_next : eachStepChar.Inv nfa wf it.next next updates) :
  eachStepChar.Inv nfa wf it.next next' updates' := by
  induction idx, hle, next, updates using eachStepChar'.go.induct' nfa wf it current with
  | base next updates => simp_all
  | found idx next updates hlt next'' matched updates'' h' found =>
    rw [eachStepChar'.go_found hlt h' found] at h
    simp_all
    exact eachStepChar.Inv.of_stepChar hlt h' (by simp [notEnd]) inv_curr inv_next
  | not_found idx next updates hlt next'' matched updates'' h' not_found ih =>
    rw [eachStepChar'.go_not_found hlt h' not_found] at h
    have inv' : eachStepChar.Inv nfa wf it.next next'' updates'' :=
      eachStepChar.Inv.of_stepChar hlt h' (by simp [notEnd]) inv_curr inv_next
    apply ih h inv'

theorem eachStepChar.inv {next next'} (h : eachStepChar' nfa wf it current next = (next', matched'))
  (notEnd : ¬it.atEnd) (empty : next.states.isEmpty)
  (inv : eachStepChar.Inv nfa wf it current.states current.updates) :
  eachStepChar.Inv nfa wf it.next next'.states next'.updates := by
  simp [eachStepChar'] at h
  set result := eachStepChar'.go nfa wf it current 0 (Nat.zero_le _) next.states next.updates
  set nextStates := result.1
  set nextUpdates := result.2.2
  have : result = (nextStates, matched', nextUpdates) := by
    simp [←h]
  exact h.1 ▸ eachStepChar.go.inv this notEnd inv (eachStepChar.Inv.of_empty empty)

end Regex.VM
