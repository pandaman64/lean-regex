import RegexCorrectness.Data.String
import RegexCorrectness.VM.Search.Basic

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (ValidPos)

namespace Regex.VM

def MatchedInv {s : String} (nfa : NFA) (wf : nfa.WellFormed) (pos₀ : ValidPos s) (matched : Option (List (Nat × ValidPos s))) : Prop :=
  (isSome : matched.isSome) →
    ∃ state pos,
      nfa[state] = .done ∧
      nfa.VMPath wf pos₀ pos state (matched.get isSome)

theorem captureNext.go.inv {s : String} {nfa wf} {pos₀ pos : ValidPos s} {matched current next matched'}
  (h : captureNext.go (HistoryStrategy s) nfa wf pos matched current next = matched')
  (le : pos₀ ≤ pos)
  (curr_inv : current.Inv nfa wf pos₀ pos) (empty : next.states.isEmpty)
  (matched_inv : MatchedInv nfa wf pos₀ matched) :
  MatchedInv nfa wf pos₀ matched' := by
  induction pos, matched, current, next using captureNext.go.induct' (HistoryStrategy s) nfa wf with
  | not_found matched current next => simp_all
  | found pos matched current next ne isEmpty isSome =>
    rw [captureNext.go_found ne isEmpty isSome] at h
    simp_all
  | ind_not_found pos matched current next ne stepped expanded isNone₁ isNone₂ ih =>
    rw [captureNext.go_ind_not_found stepped expanded rfl rfl isNone₁ isNone₂] at h
    have le' : pos₀ ≤ pos.next ne := Nat.le_trans le (ValidPos.le_of_lt pos.lt_next)
    have next_inv : stepped.2.Inv nfa wf pos₀ (pos.next ne) := eachStepChar.inv_of_inv rfl ne empty curr_inv
    have curr_inv' : expanded.2.Inv nfa wf pos₀ (pos.next ne) := εClosure.inv_of_inv rfl le' next_inv
    have matched_inv' : MatchedInv nfa wf pos₀ expanded.1 := by
      intro isSome
      have ⟨state, mem, hn, equpdate⟩ : ∃ i ∈ expanded.2.states, nfa[i] = .done ∧ expanded.2.updates[i] = expanded.1.get isSome :=
        εClosure.matched_inv rfl (by simp) isSome
      have ⟨update, path, write⟩ := curr_inv' state mem
      exact ⟨state, pos.next ne, hn, by rw [←equpdate, write (by simp [εClosure.writeUpdate, hn])]; exact path⟩
    exact ih h le' curr_inv' (by simp) matched_inv'
  | ind_found pos matched current next ne stepped hemp isSome ih =>
    rw [captureNext.go_ind_found stepped rfl hemp isSome] at h
    have curr_inv' : stepped.2.Inv nfa wf pos₀ (pos.next ne) := eachStepChar.inv_of_inv rfl ne empty curr_inv
    have matched_inv' : MatchedInv nfa wf pos₀ (stepped.1 <|> matched) := by
      match h : stepped.1 with
      | .none => simpa using matched_inv
      | .some matched' =>
        simp
        have ⟨state, mem, hn, equpdate⟩ := eachStepChar.done_of_matched_some (matched' := stepped.1) (next' := stepped.2) rfl (by simp [h])
        have ⟨update, path, write⟩ := curr_inv' state mem
        intro _
        have hwu : εClosure.writeUpdate nfa[state] := by
          simp [εClosure.writeUpdate, hn]
        exact ⟨state, pos.next ne, hn, by simp_rw [←h, ←equpdate, write hwu]; exact path⟩
    exact ih h (Nat.le_trans le (ValidPos.le_of_lt pos.lt_next)) curr_inv' (by simp) matched_inv'

/--
If `captureNext` returns `some`, the returned list corresponds to the updates of a path from
`nfa.start` to a `.done` state.
-/
theorem captureNext.path_done_of_matched {s nfa wf pos₀ matched'}
  (h : captureNext (HistoryStrategy s) nfa wf pos₀ = matched') (isSome' : matched'.isSome) :
  ∃ state pos,
    nfa[state] = .done ∧
    nfa.VMPath wf pos₀ pos state (matched'.get isSome') := by
  simp [captureNext] at h

  set result := εClosure (HistoryStrategy s) nfa wf pos₀ .none ⟨.empty, Vector.replicate nfa.nodes.size []⟩ [([], ⟨nfa.start, wf.start_lt⟩)]
  set matched := result.1
  set current := result.2
  have h' : result = (matched, current) := rfl
  have curr_inv : current.Inv nfa wf pos₀ pos₀ := εClosure.inv_of_inv h' (ValidPos.le_refl _) (.of_empty (by simp))
  have matched_inv : MatchedInv nfa wf pos₀ matched := by
    intro isSome
    have ⟨state, mem, hn, hupdate⟩ := εClosure.matched_inv h' (by simp) isSome
    have ⟨update, path, write⟩ := curr_inv state mem
    simp at hupdate
    simp [εClosure.writeUpdate, hn, hupdate] at write
    exact ⟨state, pos₀, hn, write ▸ path⟩

  exact captureNext.go.inv h (ValidPos.le_refl _) curr_inv (by simp) matched_inv isSome'

theorem SearchState.NotDoneInv.preserves {s nfa wf pos current next ne} (stepped expanded)
  (h₁ : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = stepped)
  (h₂ : εClosure (HistoryStrategy s) nfa wf (pos.next ne) .none stepped.2 [([], ⟨nfa.start, wf.start_lt⟩)] = expanded)
  (isNone₁ : stepped.1 = .none) (isNone₂ : expanded.1 = .none)
  (invCurrent : current.NotDoneInv (HistoryStrategy s) nfa) (invNext : next.NotDoneInv (HistoryStrategy s) nfa) :
  expanded.2.NotDoneInv (HistoryStrategy s) nfa := by
  have inv' := eachStepChar.not_done_of_none stepped h₁ isNone₁ invCurrent invNext
  exact εClosure.not_done_of_none expanded h₂ isNone₂ inv'

theorem SearchState.MemOfPathInv.preserves {s nfa wf pos₀ pos current next ne} (stepped expanded)
  (h₁ : eachStepChar (HistoryStrategy s) nfa wf pos ne current next = stepped)
  (h₂ : εClosure (HistoryStrategy s) nfa wf (pos.next ne) .none stepped.2 [([], ⟨nfa.start, wf.start_lt⟩)] = expanded)
  (isNone : stepped.1 = .none)
  (ndinv : current.NotDoneInv (HistoryStrategy s) nfa) (lb : εClosure.LowerBound (pos.next ne) next.states)
  (inv : current.MemOfPathInv nfa wf pos₀ pos) :
  expanded.2.MemOfPathInv nfa wf pos₀ (pos.next ne) := by
  intro k update path
  cases path with
  | init le cls => exact εClosure.mem_next h₂ (eachStepChar.lower_bound stepped h₁ lb) cls
  | @more i j k pos' _ update₁ update₂ update₃ prev step cls equpdate eqpos =>
    have : pos = pos' := ValidPos.next_inj eqpos
    subst pos'
    have mem : i ∈ current.states := inv i update₁ prev
    have mem' : k ∈ stepped.2.states :=
      eachStepChar.mem_of_step_of_none stepped h₁ isNone ndinv lb i j k update₂ mem step cls
    exact SparseSet.mem_of_mem_of_subset mem' (εClosure.subset h₂)

def NeDoneOfPathInv {s : String} (nfa : NFA) (wf : nfa.WellFormed) (pos₀ pos : ValidPos s) : Prop :=
  ∀ pos' state update, pos' ≤ pos → nfa.VMPath wf pos₀ pos' state update → nfa[state] ≠ .done

theorem NeDoneOfPathInv.preserves {s nfa wf pos₀ pos ne} {expanded : Option (List (Nat × ValidPos s)) × SearchState (HistoryStrategy s) nfa}
  (notDone : expanded.2.NotDoneInv (HistoryStrategy s) nfa) (memOfPath : expanded.2.MemOfPathInv nfa wf pos₀ (pos.next ne))
  (inv : NeDoneOfPathInv nfa wf pos₀ pos) :
  NeDoneOfPathInv nfa wf pos₀ (pos.next ne) := by
  intro pos' state update le path
  cases ValidPos.le_or_eq_of_le_next le with
  | inl le => exact inv pos' state update le path
  | inr eq =>
    have mem := memOfPath state update (eq ▸ path)
    exact notDone state mem

theorem captureNext.go.some_of_some {s nfa wf pos matched current next} (result) (h : captureNext.go (HistoryStrategy s) nfa wf pos matched current next = result)
  (isSome : matched.isSome) :
  result.isSome := by
  induction pos, matched, current, next using captureNext.go.induct' (HistoryStrategy s) nfa wf with
  | not_found matched current next =>
    rw [captureNext.go_not_found] at h
    simpa [←h] using isSome
  | found pos matched current next ne empty isSome' =>
    rw [captureNext.go_found ne empty isSome] at h
    simpa [←h] using isSome
  | ind_not_found pos matched current next ne stepped expanded isNone₁ isNone₂ ih =>
    simp [isNone₁] at isSome
  | ind_found pos matched current next ne stepped hemp isSome' ih =>
    rw [captureNext.go_ind_found stepped rfl hemp isSome'] at h
    have isSome' : (stepped.1 <|> matched).isSome := by
      match h : stepped.1 with
      | .some _ => simp
      | .none => simp [isSome]
    exact ih h isSome'

theorem captureNext.go.ne_done_of_path_of_none {s nfa wf pos₀ pos matched current next} (h : captureNext.go (HistoryStrategy s) nfa wf pos matched current next = .none)
  (isEmpty : next.states.isEmpty)
  (ndinv : current.NotDoneInv (HistoryStrategy s) nfa) (mopInv : current.MemOfPathInv nfa wf pos₀ pos)
  (inv : NeDoneOfPathInv nfa wf pos₀ pos) :
  ∀ pos' state update, nfa.VMPath wf pos₀ pos' state update → nfa[state] ≠ .done := by
  induction pos, matched, current, next using captureNext.go.induct' (HistoryStrategy s) nfa wf with
  | not_found matched current next =>
    intro pos' state update path hn
    exact inv pos' state update pos'.isValid.le_rawEndPos path hn
  | found pos matched current next ne empty isSome =>
    rw [captureNext.go_found ne empty isSome] at h
    simp [h] at isSome
  | ind_not_found pos matched current next ne stepped expanded isNone₁ isNone₂ ih =>
    rw [captureNext.go_ind_not_found stepped expanded rfl rfl isNone₁ isNone₂] at h
    have isNone₃ : expanded.1 = .none := by
      match h' : expanded.1 with
      | .none => rfl
      | .some _ =>
        have := some_of_some .none h (by simp [h'])
        simp at this
    have isEmpty' : current.states.clear.isEmpty := by simp
    have ndinv' : expanded.2.NotDoneInv (HistoryStrategy s) nfa :=
      ndinv.preserves stepped expanded rfl rfl isNone₂ isNone₃ (.of_empty isEmpty)
    have mopInv' : expanded.2.MemOfPathInv nfa wf pos₀ (pos.next ne) :=
      mopInv.preserves stepped expanded rfl rfl isNone₂ ndinv (.of_empty isEmpty)
    have inv' : NeDoneOfPathInv nfa wf pos₀ (pos.next ne) := inv.preserves ndinv' mopInv'
    exact ih h isEmpty' ndinv' mopInv' inv'
  | ind_found pos matched current next ne stepped hemp isSome ih =>
    rw [captureNext.go_ind_found stepped rfl hemp isSome] at h
    have isSome' : (stepped.1 <|> matched).isSome := by
      match h : stepped.1, matched with
      | .some _, _ => simp
      | .none, .some _ => simp
      | .none, .none => simp [h] at isSome
    have := some_of_some .none h isSome'
    simp at this

/--
If `captureNext` returns `.none`, then there is no path from `nfa.start` to a `.done` state after `it`.
-/
theorem captureNext.ne_done_of_path_of_none {s nfa wf pos} (h : captureNext (HistoryStrategy s) nfa wf pos = .none) :
  ∀ pos' state update, nfa.VMPath wf pos pos' state update → nfa[state] ≠ .done := by
  simp [captureNext] at h
  set result := εClosure (HistoryStrategy s) nfa wf pos .none ⟨.empty, Vector.replicate nfa.nodes.size []⟩ [([], ⟨nfa.start, wf.start_lt⟩)]
  match h' : result.1 with
  | .none =>
    have ndinv : SearchState.NotDoneInv (HistoryStrategy s) nfa result.2 := εClosure.not_done_of_none result rfl h' (.of_empty (by simp))
    have mopInv : SearchState.MemOfPathInv nfa wf pos pos result.2 := by
      intro i update path
      have cls := path.εClosure_of_eq_it
      exact εClosure.mem_next (matched' := result.1) (next' := result.2) rfl (.of_empty (by simp)) cls
    have inv : NeDoneOfPathInv nfa wf pos pos := by
      intro pos' state update le path
      have eq : pos = pos' := by ext; exact Nat.le_antisymm path.le le
      have mem : state ∈ result.2.states := mopInv state update (eq ▸ path)
      exact ndinv state mem
    exact captureNext.go.ne_done_of_path_of_none h rfl ndinv mopInv inv
  | .some _ =>
    have := captureNext.go.some_of_some .none h (by simp [h'])
    simp at this

end Regex.VM
