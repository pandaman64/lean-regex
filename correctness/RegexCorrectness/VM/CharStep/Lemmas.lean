import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep.Basic
import RegexCorrectness.Data.String

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.NFA (εStep' εClosure' CharStep)
open String (ValidPos)

namespace Regex.VM

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {pos : ValidPos s} {ne : pos ≠ s.endValidPos}
  {current : SearchState (HistoryStrategy s) nfa} {currentUpdates : Vector (List (Nat × ValidPos s)) nfa.nodes.size}
  {next : SearchState (HistoryStrategy s) nfa} {state : Fin nfa.nodes.size}
  {matched' : Option (List (Nat × ValidPos s))} {next' : SearchState (HistoryStrategy s) nfa}

namespace stepChar

theorem subset (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next state = (matched', next')) :
  next.states ⊆ next'.states := by
  simp only [HistoryStrategy.update_def, stepChar, Fin.getElem_fin] at h
  grind [εClosure.subset, SparseSet.subset_self]

theorem lower_bound (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next state = (matched', next'))
  (lb : εClosure.LowerBound (pos.next ne) next.states) :
  εClosure.LowerBound (pos.next ne) next'.states := by
  simp only [HistoryStrategy.update_def, stepChar, Fin.getElem_fin] at h
  grind [εClosure.lower_bound]

theorem eq_updates_of_mem_next {i k} (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next i = (matched', next'))
  (mem : k ∈ next.states) :
  next'.updates[k] = next.updates[k] := by
  simp only [HistoryStrategy.update_def, stepChar, Fin.getElem_fin] at h
  grind [εClosure.eq_updates_of_mem_next]

theorem done_of_matched_some (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next state = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  simp only [HistoryStrategy.update_def, stepChar, Fin.getElem_fin] at h
  grind [εClosure.matched_inv]

theorem mem_next_of_stepChar {i j k update}
  (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next i = (matched', next'))
  (lb : εClosure.LowerBound (pos.next ne) next.states)
  (step : nfa.CharStep pos i j) (cls : nfa.εClosure' (pos.next ne) j k update) :
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
      have ⟨_, _, hc⟩ := step
      simp [hc] at hn
    next cs state' hn' =>
      rw [NFA.CharStep.sparse hn'] at step
      have ⟨_, _, hc⟩ := step
      simp [hc] at hn
    next ne₁ ne₂ =>
      have := step.char_or_sparse
      simp_all only [Prod.mk.injEq, imp_false, Fin.getElem_fin, exists_const, or_self]

theorem write_updates_of_mem_next {i k}
  (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next i = (matched', next'))
  (ne : pos ≠ s.endValidPos) (mem : k ∈ next'.states) :
  k ∈ next.states ∨ ∃ j update',
    nfa.CharStep pos i j ∧
    nfa.εClosure' (pos.next ne) j k update' ∧
    (εClosure.writeUpdate nfa[k] → next'.updates[k] = currentUpdates.get i ++ update') := by
  simp [stepChar] at h
  split at h
  next state' hn =>
    match εClosure.write_updates_of_mem_next h mem with
    | .inl mem => exact .inl mem
    | .inr ⟨update', cls, write⟩ => exact .inr ⟨state', update', (by grind), cls, write⟩
  next => grind

theorem inv {pos₀ idx} (hlt : idx < current.states.count)
  (h : stepChar (HistoryStrategy s) nfa wf pos ne current.updates next current.states[idx] = (matched', next'))
  (ne : pos ≠ s.endValidPos)
  (invCurrent : current.Inv nfa wf pos₀ pos)
  (invNext : next.Inv nfa wf pos₀ (pos.next ne)) :
  next'.Inv nfa wf pos₀ (pos.next ne) := by
  have ⟨update, path, write⟩ := invCurrent current.states[idx] (SparseSet.mem_get hlt)

  intro k mem
  match stepChar.write_updates_of_mem_next h ne mem with
  | .inl mem =>
    have inv := invNext k mem
    have equ := stepChar.eq_updates_of_mem_next h mem
    exact equ ▸ inv
  | .inr ⟨j, update', step, cls, write'⟩ =>
    have write'' : εClosure.writeUpdate nfa[k] → next'.updates[k] = update ++ update' := (write step.write_update) ▸ write'
    exact ⟨update ++ update', .more path step cls rfl rfl, write''⟩

theorem not_done_of_none (result) (h : stepChar (HistoryStrategy s) nfa wf pos ne currentUpdates next state = result)
  (isNone : result.1 = .none)
  (inv : next.NotDoneInv (HistoryStrategy s) nfa) :
  result.2.NotDoneInv (HistoryStrategy s) nfa := by
  simp only [HistoryStrategy.update_def, stepChar, Fin.getElem_fin] at h
  split at h
  next state' hn => exact εClosure.not_done_of_none result h isNone inv
  next => simpa [←h] using inv

end stepChar

namespace eachStepChar

theorem go.lower_bound {idx hle} (h : eachStepChar.go (HistoryStrategy s) nfa wf pos ne current idx hle next = (matched', next'))
  (lb : εClosure.LowerBound (pos.next ne) next.states) :
  εClosure.LowerBound (pos.next ne) next'.states := by
  induction idx, hle, next using eachStepChar.go.induct' (HistoryStrategy s) nfa wf pos ne current with
  | base next => simp_all
  | done i hlt next hn => simp_all
  | found i hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp_all
    exact stepChar.lower_bound h' lb
  | not_found i hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    exact ih h (stepChar.lower_bound h' lb)

theorem go.done_of_matched_some {idx hle} (h : eachStepChar.go (HistoryStrategy s) nfa wf pos ne current idx hle next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' := by
  induction idx, hle, next using eachStepChar.go.induct' (HistoryStrategy s) nfa wf pos ne current with
  | base next => grind
  | done i hlt next hn => grind
  | found i hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp at h
    simp [h] at h'
    exact stepChar.done_of_matched_some h' isSome'
  | not_found i hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    exact ih h

theorem go.inv {pos₀ idx hle} (h : eachStepChar.go (HistoryStrategy s) nfa wf pos ne current idx hle next = (matched', next'))
  (ne : pos ≠ s.endValidPos)
  (invCurrent : current.Inv nfa wf pos₀ pos)
  (invNext : next.Inv nfa wf pos₀ (pos.next ne)) :
  next'.Inv nfa wf pos₀ (pos.next ne) := by
  induction idx, hle, next using eachStepChar.go.induct' (HistoryStrategy s) nfa wf pos ne current with
  | base next => simp_all
  | done i hlt next hn => simp_all
  | found idx hlt next hn matched next'' h' found =>
    rw [eachStepChar.go_found hlt hn h' found] at h
    simp_all
    exact stepChar.inv hlt h' ne invCurrent invNext
  | not_found idx hlt next hn matched next'' h' not_found ih =>
    rw [eachStepChar.go_not_found hlt hn h' not_found] at h
    have inv' : next''.Inv nfa wf pos₀ (pos.next ne) :=
      stepChar.inv hlt h' ne invCurrent invNext
    apply ih h inv'

theorem go.not_done_of_none {idx hle} (result) (h : eachStepChar.go (HistoryStrategy s) nfa wf pos ne current idx hle next = result)
  (isNone : result.1 = .none)
  (invCurrent : current.NotDoneInv (HistoryStrategy s) nfa) (invNext : next.NotDoneInv (HistoryStrategy s) nfa) :
  result.2.NotDoneInv (HistoryStrategy s) nfa := by
  induction idx, hle, next using eachStepChar.go.induct' (HistoryStrategy s) nfa wf pos ne current with
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

theorem go.subset {idx hle} (h : eachStepChar.go (HistoryStrategy s) nfa wf pos ne current idx hle next = (matched', next')) :
  next.states ⊆ next'.states := by
  induction idx, hle, next using eachStepChar.go.induct' (HistoryStrategy s) nfa wf pos ne current with
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

theorem go.mem_of_step_of_none {idx hle} (result) (h : eachStepChar.go (HistoryStrategy s) nfa wf pos ne current idx hle next = result)
  (isNone : result.1 = .none)
  (notDone : current.NotDoneInv (HistoryStrategy s) nfa)
  (lb : εClosure.LowerBound (pos.next ne) next.states)
  (inv : ∀ i state' state'' update (_ : i < current.states.count), i < idx → nfa.CharStep pos current.states[i] state' → nfa.εClosure' (pos.next ne) state' state'' update → state'' ∈ result.2.states) :
  ∀ state state' state'' update, state ∈ current.states → nfa.CharStep pos state state' → nfa.εClosure' (pos.next ne) state' state'' update → state'' ∈ result.2.states := by
  induction idx, hle, next using eachStepChar.go.induct' (HistoryStrategy s) nfa wf pos ne current with
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
    have lb' : εClosure.LowerBound (pos.next ne) next''.states := stepChar.lower_bound h' lb
    have inv' (i : Nat) (state' state'' update) (isLt : i < current.states.count) (hlt : i < idx + 1)
      (step : nfa.CharStep pos current.states[i] state') (cls : nfa.εClosure' (pos.next ne) state' state'' update) :
      state'' ∈ result.2.states := by
      have : i < idx ∨ i = idx := Nat.lt_succ_iff_lt_or_eq.mp hlt
      cases this with
      | inl hlt => exact inv i state' state'' update isLt hlt step cls
      | inr eq =>
        have mem'' : state'' ∈ next''.states := stepChar.mem_next_of_stepChar h' lb (eq ▸ step) cls
        exact SparseSet.mem_of_mem_of_subset mem'' (go.subset h)
    exact ih h lb' inv'

theorem lower_bound (result) (h : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = result)
  (lb : εClosure.LowerBound (pos.next ne) next.states) :
  εClosure.LowerBound (pos.next ne) result.2.states := by
  simp [eachStepChar] at h
  exact go.lower_bound h lb

theorem done_of_matched_some (h : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = (matched', next'))
  (isSome' : matched'.isSome) :
  ∃ state' ∈ next'.states, nfa[state'] = .done ∧ next'.updates[state'] = matched'.get isSome' :=
  go.done_of_matched_some h isSome'

theorem inv_of_inv {pos₀ next next'} (h : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = (matched', next'))
  (ne : pos ≠ s.endValidPos) (empty : next.states.isEmpty)
  (inv : current.Inv nfa wf pos₀ pos) :
  next'.Inv nfa wf pos₀ (pos.next ne) := by
  simp [eachStepChar] at h
  exact go.inv h ne inv (.of_empty empty)

theorem not_done_of_none (result) (h : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = result)
  (isNone : result.1 = .none)
  (invCurrent : current.NotDoneInv (HistoryStrategy s) nfa) (invNext : next.NotDoneInv (HistoryStrategy s) nfa) :
  result.2.NotDoneInv (HistoryStrategy s) nfa := by
  simp [eachStepChar] at h
  exact go.not_done_of_none result h isNone invCurrent invNext

-- Intended usage: given `inv : current.MemOfPathInv nfa wf pos₀ pos`, if there is a VMPath for `pos.next ne`. We cases on the path.
-- If that results in a char step and εClosure, we can use this theorem to show that the state is in `next'.states`.
theorem mem_of_step_of_none (result) (h : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = result)
  (isNone : result.1 = .none)
  (notDone : current.NotDoneInv (HistoryStrategy s) nfa)
  (lb : εClosure.LowerBound (pos.next ne) next.states) :
  ∀ state state' state'' update, state ∈ current.states → nfa.CharStep pos state state' → nfa.εClosure' (pos.next ne) state' state'' update → state'' ∈ result.2.states := by
  simp [eachStepChar] at h
  exact go.mem_of_step_of_none result h isNone notDone lb (by simp only [Nat.not_lt_zero, IsEmpty.forall_iff, implies_true])

end eachStepChar

end Regex.VM
