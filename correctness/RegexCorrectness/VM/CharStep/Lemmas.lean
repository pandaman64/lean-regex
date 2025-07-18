import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep.Basic
import RegexCorrectness.Data.String

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.NFA (εStep' εClosure' CharStep)
open String (Pos Iterator)

namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator}
  {current : SearchState HistoryStrategy nfa} {currentUpdates : Vector (List (Nat × Pos)) nfa.nodes.size}
  {next : SearchState HistoryStrategy nfa} {state : Fin nfa.nodes.size}
  {matched' : Option (List (Nat × Pos))} {next' : SearchState HistoryStrategy nfa}

namespace stepChar

theorem subset (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = (matched', next')) :
  next.states ⊆ next'.states := by
  simp [stepChar] at h
  split at h
  next state' hn => exact εClosure.subset h
  next => simp_all [SparseSet.subset_self]

theorem lower_bound (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = (matched', next'))
  (lb : εClosure.LowerBound it.next next.states) :
  εClosure.LowerBound it.next next'.states := by
  simp [stepChar] at h
  split at h
  next state' hn => exact εClosure.lower_bound h lb
  next => simp_all

theorem eq_updates_of_mem_next {i k} (h : stepChar HistoryStrategy nfa wf it currentUpdates next i = (matched', next'))
  (mem : k ∈ next.states) :
  next'.updates[k] = next.updates[k] := by
  simp [stepChar] at h
  split at h
  next state' hn => exact εClosure.eq_updates_of_mem_next h mem
  next => simp_all

theorem done_of_matched_some (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  simp [stepChar] at h
  split at h
  next state' hn => exact εClosure.matched_inv h (by simp) isSome'
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
  next state' hn =>
    have eqj : j = state' := by
      split at hn
      next hn' =>
        simp at hn
        simp [NFA.CharStep.char hn'] at step
        simp [Fin.ext_iff, step, ←hn.2]
      next hn' =>
        simp at hn
        simp [NFA.CharStep.sparse hn'] at step
        simp [Fin.ext_iff, step, ←hn.2]
      next => simp at hn
    exact εClosure.mem_next h lb (eqj ▸ cls)
  next hn =>
    split at hn
    next c state' hn' =>
      rw [NFA.CharStep.char hn'] at step
      have ⟨_, _, _, vf⟩ := step
      simp [vf.curr] at hn
    next cs state' hn' =>
      rw [NFA.CharStep.sparse hn'] at step
      have ⟨_, c, _, _, vf, hc⟩ := step
      simp [vf.curr, hc] at hn
    next ne₁ ne₂ =>
      have := step.char_or_sparse
      simp_all only [Prod.mk.injEq, imp_false, Fin.getElem_fin, exists_const, or_self]

theorem write_updates_of_mem_next {i k}
  (h : stepChar HistoryStrategy nfa wf it currentUpdates next i = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd) (mem : k ∈ next'.states) :
  k ∈ next.states ∨ ∃ j update',
    nfa.CharStep it i j ∧
    nfa.εClosure' it.next j k update' ∧
    (εClosure.writeUpdate nfa[k] → next'.updates[k] = currentUpdates.get i ++ update') := by
  simp [stepChar] at h
  split at h
  next state' hn =>
    have hasNext := it.hasNext_of_not_atEnd notEnd
    have ⟨l, r, vf⟩ := v.validFor_of_hasNext hasNext
    have v' : it.next.Valid := v.next hasNext
    have := εClosure.write_updates_of_mem_next h v' mem
    match this with
    | .inl mem => exact .inl mem
    | .inr ⟨update', cls, write⟩ =>
      refine .inr ⟨state', update', ?_, cls, write⟩
      split at hn
      next c state' hn' =>
        simp at hn
        rw [NFA.CharStep.char hn']
        exact ⟨l, r, by simp [←hn.2], hn.1 ▸ vf⟩
      next cs state' hn' =>
        simp at hn
        rw [NFA.CharStep.sparse hn']
        exact ⟨l, it.curr, r, by simp [←hn.2], vf, hn.1⟩
      next => simp at hn
  next => simp_all only [Bool.not_eq_true, SparseSet.mem_mem, Prod.mk.injEq, Fin.getElem_fin, exists_and_left, true_or]

theorem inv {it₀ idx} (hlt : idx < current.states.count)
  (h : stepChar HistoryStrategy nfa wf it current.updates next current.states[idx] = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd)
  (invCurrent : current.Inv nfa wf it₀ it)
  (invNext : next.Inv nfa wf it₀ it.next) :
  next'.Inv nfa wf it₀ it.next := by
  have ⟨update, path, write⟩ := invCurrent current.states[idx] (SparseSet.mem_get hlt)

  intro k mem
  have := stepChar.write_updates_of_mem_next h v (by simp [notEnd]) mem
  match this with
  | .inl mem =>
    have inv := invNext k mem
    have equ := stepChar.eq_updates_of_mem_next h mem
    exact equ ▸ inv
  | .inr ⟨j, update', step, cls, write'⟩ =>
    have write'' : εClosure.writeUpdate nfa[k] → next'.updates[k] = update ++ update' := (write step.write_update) ▸ write'
    exact ⟨update ++ update', .more path step cls rfl rfl, write''⟩

theorem not_done_of_none (result) (h : stepChar HistoryStrategy nfa wf it currentUpdates next state = result)
  (isNone : result.1 = .none)
  (inv : next.NotDoneInv HistoryStrategy nfa) :
  result.2.NotDoneInv HistoryStrategy nfa := by
  simp [stepChar] at h
  split at h
  next state' hn => exact εClosure.not_done_of_none result h isNone inv
  next => simpa [←h] using inv

end stepChar

namespace eachStepChar

theorem go.lower_bound {idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next'))
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

theorem go.done_of_matched_some {idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next'))
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

theorem go.inv {it₀ idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd)
  (invCurrent : current.Inv nfa wf it₀ it)
  (invNext : next.Inv nfa wf it₀ it.next) :
  next'.Inv nfa wf it₀ it.next := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next => simp_all
  | done i hlt next hn => simp_all
  | found idx hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp_all
    exact stepChar.inv hlt h' v (by simp [notEnd]) invCurrent invNext
  | not_found idx hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    have inv' : next''.Inv nfa wf it₀ it.next :=
      stepChar.inv hlt h' v (by simp [notEnd]) invCurrent invNext
    apply ih h inv'

theorem go.not_done_of_none {idx hle} (result) (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = result)
  (isNone : result.1 = .none)
  (invCurrent : current.NotDoneInv HistoryStrategy nfa) (invNext : next.NotDoneInv HistoryStrategy nfa) :
  result.2.NotDoneInv HistoryStrategy nfa := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next => simpa [←h] using invNext
  | done i hlt next hn => exact (invCurrent current.states[i] (SparseSet.mem_get hlt) hn).elim
  | found i hlt next hn matched next'' h' found =>
    simp [eachStepChar.go_found hlt hn h' found] at h
    simp [h] at h'
    exact stepChar.not_done_of_none result h' isNone invNext
  | not_found i hlt next hn matched next'' h' notFound ih =>
    simp [eachStepChar.go_not_found hlt hn h' notFound] at h
    simp at notFound
    have invNext' := stepChar.not_done_of_none (matched, next'') h' notFound invNext
    exact ih h invNext'

theorem go.subset {idx hle} (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = (matched', next')) :
  next.states ⊆ next'.states := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next =>
    simp [eachStepChar.go_base] at h
    exact h.2 ▸ SparseSet.subset_self
  | done i hlt next hn =>
    simp [eachStepChar.go_done hlt hn] at h
    exact h.2 ▸ SparseSet.subset_self
  | found i hlt next hn matched next'' h' found =>
    simp [eachStepChar.go_found hlt hn h' found] at h
    exact h.2 ▸ stepChar.subset h'
  | not_found i hlt next hn matched next'' h' notFound ih =>
    simp [eachStepChar.go_not_found hlt hn h' notFound] at h
    exact SparseSet.subset_trans (stepChar.subset h') (ih h)

theorem go.mem_of_step_of_none {idx hle} (result) (h : eachStepChar.go HistoryStrategy nfa wf it current idx hle next = result)
  (isNone : result.1 = .none)
  (notDone : current.NotDoneInv HistoryStrategy nfa)
  (lb : εClosure.LowerBound it.next next.states)
  (inv : ∀ i state' state'' update (_ : i < current.states.count), i < idx → nfa.CharStep it current.states[i] state' → nfa.εClosure' it.next state' state'' update → state'' ∈ result.2.states) :
  ∀ state state' state'' update, state ∈ current.states → nfa.CharStep it state state' → nfa.εClosure' it.next state' state'' update → state'' ∈ result.2.states := by
  induction idx, hle, next using eachStepChar.go.induct' HistoryStrategy nfa wf it current with
  | base next =>
    simp [eachStepChar.go_base] at h
    intro state state' state'' update mem step cls
    have ⟨isLt, eq⟩ := SparseSet.index_of_mem mem
    exact inv (current.states.index state) state' state'' update isLt isLt (by simpa [eq] using step) cls
  | done idx hlt next hn => exact (notDone current.states[idx] (SparseSet.mem_get hlt) hn).elim
  | found idx hlt next hn matched next'' h' found =>
    simp [eachStepChar.go_found hlt hn h' found] at h
    simp [←h] at isNone
    simp [isNone] at found
  | not_found idx hlt next hn matched next'' h' notFound ih =>
    rw [eachStepChar.go_not_found hlt hn h' notFound] at h
    have lb' : εClosure.LowerBound it.next next''.states := stepChar.lower_bound h' lb
    have inv' (i : Nat) (state' state'' update) (isLt : i < current.states.count) (hlt : i < idx + 1)
      (step : nfa.CharStep it current.states[i] state') (cls : nfa.εClosure' it.next state' state'' update) :
      state'' ∈ result.2.states := by
      have : i < idx ∨ i = idx := Nat.lt_succ_iff_lt_or_eq.mp hlt
      cases this with
      | inl hlt => exact inv i state' state'' update isLt hlt step cls
      | inr eq =>
        have mem'' : state'' ∈ next''.states := stepChar.mem_next_of_stepChar h' lb (eq ▸ step) cls
        exact SparseSet.mem_of_mem_of_subset mem'' (go.subset h)
    exact ih h lb' inv'

theorem lower_bound (result) (h : eachStepChar HistoryStrategy nfa wf it current next = result)
  (lb : εClosure.LowerBound it.next next.states) :
  εClosure.LowerBound it.next result.2.states := by
  simp [eachStepChar] at h
  exact go.lower_bound h lb

theorem done_of_matched_some (h : eachStepChar HistoryStrategy nfa wf it current next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' :=
  go.done_of_matched_some h isSome'

theorem inv_of_inv {it₀ next next'} (h : eachStepChar HistoryStrategy nfa wf it current next = (matched', next'))
  (v : it.Valid) (notEnd : ¬it.atEnd) (empty : next.states.isEmpty)
  (inv : current.Inv nfa wf it₀ it) :
  next'.Inv nfa wf it₀ it.next := by
  simp [eachStepChar] at h
  exact go.inv h v notEnd inv (.of_empty empty)

theorem not_done_of_none (result) (h : eachStepChar HistoryStrategy nfa wf it current next = result)
  (isNone : result.1 = .none)
  (invCurrent : current.NotDoneInv HistoryStrategy nfa) (invNext : next.NotDoneInv HistoryStrategy nfa) :
  result.2.NotDoneInv HistoryStrategy nfa := by
  simp [eachStepChar] at h
  exact go.not_done_of_none result h isNone invCurrent invNext

-- Intended usage: given `inv : current.MemOfPathInv nfa wf it₀ it`, if there is a VMPath for `it.next`. We cases on the path.
-- If that results in a char step and εClosure, we can use this theorem to show that the state is in `next'.states`.
theorem mem_of_step_of_none (result) (h : eachStepChar HistoryStrategy nfa wf it current next = result)
  (isNone : result.1 = .none)
  (notDone : current.NotDoneInv HistoryStrategy nfa)
  (lb : εClosure.LowerBound it.next next.states) :
  ∀ state state' state'' update, state ∈ current.states → nfa.CharStep it state state' → nfa.εClosure' it.next state' state'' update → state'' ∈ result.2.states := by
  simp [eachStepChar] at h
  exact go.mem_of_step_of_none result h isNone notDone lb (by simp only [Nat.not_lt_zero, IsEmpty.forall_iff, implies_true])

end eachStepChar

end Regex.VM
