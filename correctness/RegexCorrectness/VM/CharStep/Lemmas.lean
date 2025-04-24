import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep.Basic

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.NFA (εStep' εClosure' CharStep)
open String (Pos Iterator)

namespace Regex.VM

local instance : Strategy := HistoryStrategy

variable {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {current : SearchState HistoryStrategy nfa} {currentUpdates : Vector (List (Nat × Pos)) nfa.nodes.size}
  {next : SearchState HistoryStrategy nfa} {state : Fin nfa.nodes.size}
  {matched' : Option (List (Nat × Pos))} {next' : SearchState HistoryStrategy nfa}

theorem stepChar.subset (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = (matched', next')) :
  next.states ⊆ next'.states := by
  simp [stepChar] at h
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

theorem stepChar.lower_bound (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = (matched', next'))
  (lb : εClosure.LowerBound it.next next.states) :
  εClosure.LowerBound it.next next'.states := by
  simp [stepChar] at h
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

theorem stepChar.eq_updates_of_mem_next {i k} (h : stepChar HistoryStrategy nfa wf it currentUpdates next i = (matched', next'))
  (mem : k ∈ next.states) :
  next'.updates[k] = next.updates[k] := by
  simp [stepChar] at h
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

theorem stepChar.done_of_matched_some (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  simp [stepChar] at h
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

theorem mem_next_of_stepChar {i j k update}
  (h : stepChar HistoryStrategy nfa wf it currentUpdates next i = (matched', next'))
  (lb : εClosure.LowerBound it.next next.states)
  (step : nfa.CharStep it i j) (cls : nfa.εClosure' it.next j k update) :
  k ∈ next'.states := by
  simp [stepChar] at h
  split at h
  next c' j' hn =>
    rw [CharStep.char hn] at step
    have ⟨l, r, eqj, vf⟩ := step
    simp [vf.curr] at h
    exact mem_next_of_εClosure h lb (by simpa [←eqj] using cls)
  next cs j' hn =>
    rw [CharStep.sparse hn] at step
    have ⟨l, c, r, eqj, vf, hc⟩ := step
    simp [vf.curr, hc] at h
    exact mem_next_of_εClosure h lb (by simpa [←eqj] using cls)
  next ne₁ ne₂ =>
    have := step.char_or_sparse
    simp_all

theorem stepChar.write_updates_of_mem_next {i k}
  (h : stepChar HistoryStrategy nfa wf it currentUpdates next i = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd) (mem : k ∈ next'.states) :
  k ∈ next.states ∨ ∃ j update',
    nfa.CharStep it i j ∧
    nfa.εClosure' it.next j k update' ∧
    (WriteUpdate k → next'.updates[k] = currentUpdates.get i ++ update') := by
  simp [stepChar] at h
  split at h
  next c j hn =>
    split at h
    next eqc =>
      subst c
      have ⟨l, r, vf⟩ := v.validFor
      match r with
      | [] => simp [vf.atEnd] at notEnd
      | c :: r =>
        have curr : it.curr = c := vf.curr
        have := εClosure.write_updates_of_mem_next h (v.next (it.hasNext_of_not_atEnd notEnd)) mem
        match this with
        | .inl mem => exact .inl mem
        | .inr ⟨update', cls, write⟩ =>
          have isLt := wf.inBounds' i hn
          exact .inr ⟨⟨j, isLt⟩, update', NFA.Step.char (Nat.zero_le _) i.isLt hn (curr ▸ vf), cls, write⟩
    next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]
  next cs j hn =>
    split at h
    next hc =>
      have ⟨l, r, vf⟩ := v.validFor
      match r with
      | [] => simp [vf.atEnd] at notEnd
      | c :: r =>
        have curr : it.curr = c := vf.curr
        have := εClosure.write_updates_of_mem_next h (v.next (it.hasNext_of_not_atEnd notEnd)) mem
        match this with
        | .inl mem => exact .inl mem
        | .inr ⟨update', cls, write⟩ =>
          have isLt := wf.inBounds' i hn
          exact .inr ⟨⟨j, isLt⟩, update', NFA.Step.sparse (Nat.zero_le _) i.isLt hn (curr ▸ vf) hc, cls, write⟩
    next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]
  next => simp_all only [SparseSet.mem_mem, Prod.mk.injEq, exists_and_left, true_or]

theorem eachStepChar.go.lower_bound {idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next'))
  (lb : εClosure.LowerBound it.next next.states) :
  εClosure.LowerBound it.next next'.states := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next => simp_all
  | done i hlt next hn => simp_all
  | found i hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp_all
    exact stepChar.lower_bound h' lb
  | not_found i hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    exact ih h (stepChar.lower_bound h' lb)

theorem eachStepChar.go.done_of_matched_some {idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next =>
    simp at h
    simp [←h.1] at isSome'
  | done i hlt next hn =>
    simp [hlt, hn] at h
    simp [←h.1] at isSome'
  | found i hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp at h
    simp [h] at h'
    exact stepChar.done_of_matched_some h' isSome'
  | not_found i hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    exact ih h

theorem eachStepChar.done_of_matched_some (h : eachStepChar HistoryStrategy nfa wf it current next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome'  :=
  eachStepChar.go.done_of_matched_some h isSome'

theorem eachStepChar.inv_of_stepChar {idx} (hlt : idx < current.states.count)
  (h : stepChar HistoryStrategy nfa wf it current.updates next current.states[idx] = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd)
  (inv_curr : current.Inv nfa wf it)
  (inv_next : next.Inv nfa wf it.next) :
  next'.Inv nfa wf it.next := by
  have ⟨update, path, write⟩ := inv_curr current.states[idx] (SparseSet.mem_get hlt)

  intro k mem
  have := stepChar.write_updates_of_mem_next h v (by simp [notEnd]) mem
  match this with
  | .inl mem =>
    have inv := inv_next k mem
    have equ := stepChar.eq_updates_of_mem_next h mem
    exact equ ▸ inv
  | .inr ⟨j, update', step, cls, write'⟩ =>
    simp [step.write_update] at write
    have write'' : WriteUpdate k → next'.updates[k] = update ++ update' := write ▸ write'
    exact ⟨update ++ update', .more path step cls, write''⟩

theorem eachStepChar.go.inv {idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd)
  (inv_curr : current.Inv nfa wf it)
  (inv_next : next.Inv nfa wf it.next) :
  next'.Inv nfa wf it.next := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next => simp_all
  | done i hlt next hn => simp_all
  | found idx hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp_all
    exact eachStepChar.inv_of_stepChar hlt h' v (by simp [notEnd]) inv_curr inv_next
  | not_found idx hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    have inv' : next''.Inv nfa wf it.next :=
      eachStepChar.inv_of_stepChar hlt h' v (by simp [notEnd]) inv_curr inv_next
    apply ih h inv'

theorem eachStepChar.inv_of_inv {next next'} (h : eachStepChar HistoryStrategy nfa wf it current next = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd) (empty : next.states.isEmpty)
  (inv : current.Inv nfa wf it) :
  next'.Inv nfa wf it.next := by
  simp [eachStepChar] at h
  exact eachStepChar.go.inv h v notEnd inv (.of_empty empty)

end Regex.VM
