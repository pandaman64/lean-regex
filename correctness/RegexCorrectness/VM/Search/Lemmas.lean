import RegexCorrectness.Data.String
import RegexCorrectness.VM.Search.Basic

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

def MatchedInv (nfa : NFA) (wf : nfa.WellFormed) (it₀ : Iterator) (matched : Option (List (Nat × Pos))) : Prop :=
  (isSome : matched.isSome) →
    ∃ state it,
      nfa[state] = .done ∧
      nfa.VMPath wf it₀ it state (matched.get isSome)

theorem captureNext.go.inv {nfa wf it₀ it matched current next matched'}
  (h : captureNext.go HistoryStrategy nfa wf it matched current next = matched')
  (v : it.Valid) (eqs : it.toString = it₀.toString) (le : it₀.pos ≤ it.pos)
  (curr_inv : current.Inv nfa wf it₀ it) (empty : next.states.isEmpty)
  (matched_inv : MatchedInv nfa wf it₀ matched) :
  MatchedInv nfa wf it₀ matched' := by
  induction it, matched, current, next using captureNext.go.induct' HistoryStrategy nfa wf with
  | not_found it matched current next atEnd => simp_all
  | found it matched current next atEnd empty' some =>
    rw [captureNext.go_found atEnd empty' some] at h
    simp_all
  | ind_not_found it matched current next stepped expanded atEnd isNone₁ isNone₂ ih =>
    rw [captureNext.go_ind_not_found stepped expanded rfl rfl atEnd isNone₁ isNone₂] at h
    have le' : it₀.pos ≤ it.next.pos := Nat.le_trans le (Nat.le_of_lt it.lt_next)
    have v' : it.next.Valid := v.next (it.hasNext_of_not_atEnd atEnd)
    have next_inv : stepped.2.Inv nfa wf it₀ it.next := eachStepChar.inv_of_inv rfl v atEnd empty curr_inv
    have curr_inv' : expanded.2.Inv nfa wf it₀ it.next := εClosure.inv_of_inv rfl eqs le' v' next_inv
    have matched_inv' : MatchedInv nfa wf it₀ expanded.1 := by
      intro isSome
      have ⟨state, mem, hn, equpdate⟩ : ∃ i ∈ expanded.2.states, nfa[i] = .done ∧ expanded.2.updates[i] = expanded.1.get isSome :=
        εClosure.matched_inv rfl (by simp) isSome
      have ⟨update, path, write⟩ := curr_inv' state mem
      exact ⟨state, it.next, hn, by rw [←equpdate, write (by simp [εClosure.writeUpdate, hn])]; exact path⟩
    exact ih h v' eqs le' curr_inv' (by simp) matched_inv'
  | ind_found it matched current next stepped atEnd hemp isSome ih =>
    rw [captureNext.go_ind_found stepped rfl atEnd hemp isSome] at h
    have curr_inv' : stepped.2.Inv nfa wf it₀ it.next := eachStepChar.inv_of_inv rfl v atEnd empty curr_inv
    have matched_inv' : MatchedInv nfa wf it₀ (stepped.1 <|> matched) := by
      match h : stepped.1 with
      | .none => simpa using matched_inv
      | .some matched' =>
        simp
        have ⟨state, mem, hn, equpdate⟩ := eachStepChar.done_of_matched_some (matched' := stepped.1) (next' := stepped.2) rfl (by simp [h])
        have ⟨update, path, write⟩ := curr_inv' state mem
        intro _
        exact ⟨state, it.next, hn, by simpa [←h, ←equpdate, write (by simp [εClosure.writeUpdate, hn])] using path⟩
    exact ih h (v.next (it.hasNext_of_not_atEnd atEnd)) eqs (Nat.le_trans le (Nat.le_of_lt it.lt_next)) curr_inv' (by simp) matched_inv'

/--
If `captureNext` returns `some`, the returned list corresponds to the updates of a path from
`nfa.start` to a `.done` state.
-/
theorem captureNext.path_done_of_matched {nfa wf it₀ matched'}
  (h : captureNext HistoryStrategy nfa wf it₀ = matched') (v : it₀.Valid) (isSome' : matched'.isSome) :
  ∃ state it,
    nfa[state] = .done ∧
    nfa.VMPath wf it₀ it state (matched'.get isSome') := by
  simp [captureNext] at h

  set result := εClosure HistoryStrategy nfa wf it₀ .none ⟨.empty, Vector.mkVector nfa.nodes.size []⟩ [([], ⟨nfa.start, wf.start_lt⟩)]
  set matched := result.1
  set current := result.2
  have h' : result = (matched, current) := rfl
  have curr_inv : current.Inv nfa wf it₀ it₀ := εClosure.inv_of_inv h' rfl (Nat.le_refl _) v (.of_empty (by simp))
  have matched_inv : MatchedInv nfa wf it₀ matched := by
    intro isSome
    have ⟨state, mem, hn, hupdate⟩ := εClosure.matched_inv h' (by simp) isSome
    have ⟨update, path, write⟩ := curr_inv state mem
    simp [εClosure.writeUpdate, hn, hupdate] at write
    exact ⟨state, it₀, hn, write ▸ path⟩

  exact captureNext.go.inv h v rfl (Nat.le_refl _) curr_inv (by simp) matched_inv isSome'

theorem SearchState.NotDoneInv.preserves {nfa wf it current next} (stepped expanded)
  (h₁ : eachStepChar HistoryStrategy nfa wf it current next = stepped)
  (h₂ : εClosure HistoryStrategy nfa wf it.next .none stepped.2 [([], ⟨nfa.start, wf.start_lt⟩)] = expanded)
  (isNone₁ : stepped.1 = .none) (isNone₂ : expanded.1 = .none)
  (invCurrent : current.NotDoneInv HistoryStrategy nfa) (invNext : next.NotDoneInv HistoryStrategy nfa) :
  expanded.2.NotDoneInv HistoryStrategy nfa := by
  have inv' := eachStepChar.not_done_of_none stepped h₁ isNone₁ invCurrent invNext
  exact εClosure.not_done_of_none expanded h₂ isNone₂ inv'

theorem SearchState.MemOfPathInv.preserves {nfa wf it₀ it current next} (stepped expanded)
  (h₁ : eachStepChar HistoryStrategy nfa wf it current next = stepped)
  (h₂ : εClosure HistoryStrategy nfa wf it.next .none stepped.2 [([], ⟨nfa.start, wf.start_lt⟩)] = expanded)
  (isNone : stepped.1 = .none) (v : it.Valid)
  (ndinv : current.NotDoneInv HistoryStrategy nfa) (lb : εClosure.LowerBound it.next next.states)
  (inv : current.MemOfPathInv nfa wf it₀ it) :
  expanded.2.MemOfPathInv nfa wf it₀ it.next := by
  intro k update path
  cases path with
  | init eqs le cls => exact εClosure.mem_next h₂ (eachStepChar.lower_bound stepped h₁ lb) cls
  | @more i j k it' _ update₁ update₂ update₃ prev step cls equpdate eqit =>
    have : it = it' := Iterator.eq_of_valid_of_next_eq v step.validL eqit
    subst it'
    have mem : i ∈ current.states := inv i update₁ prev
    have mem' : k ∈ stepped.2.states :=
      eachStepChar.mem_of_step_of_none stepped h₁ isNone ndinv lb i j k update₂ mem step cls
    exact SparseSet.mem_of_mem_of_subset mem' (εClosure.subset h₂)

def NeDoneOfPathInv (nfa : NFA) (wf : nfa.WellFormed) (it₀ it : Iterator) : Prop :=
  ∀ it' state update, it'.pos ≤ it.pos → nfa.VMPath wf it₀ it' state update → nfa[state] ≠ .done

theorem NeDoneOfPathInv.preserves {nfa wf it₀ it} {expanded : Option (List (Nat × Pos)) × SearchState HistoryStrategy nfa}
  (eqs : it.toString = it₀.toString) (v : it.Valid)
  (notDone : expanded.2.NotDoneInv HistoryStrategy nfa) (memOfPath : expanded.2.MemOfPathInv nfa wf it₀ it.next)
  (inv : NeDoneOfPathInv nfa wf it₀ it) :
  NeDoneOfPathInv nfa wf it₀ it.next := by
  intro it' state update le path
  have : it'.pos ≤ it.pos ∨ it' = it.next := by
    have eqs' : it'.toString = it.toString := by
      rw [eqs, path.toString]
    have v' : it'.Valid := path.valid
    cases v'.pos_le_or_ge_next v eqs' with
    | inl le => exact .inl le
    | inr ge =>
      have eq : it'.pos = it.next.pos := by simpa [Pos.ext_iff] using Nat.le_antisymm le ge
      exact .inr (Iterator.ext eqs' eq)
  cases this with
  | inl le => exact inv it' state update le path
  | inr eq =>
    have mem := memOfPath state update (eq ▸ path)
    exact notDone state mem

theorem captureNext.go.some_of_some {nfa wf it matched current next} (result) (h : captureNext.go HistoryStrategy nfa wf it matched current next = result)
  (isSome : matched.isSome) :
  result.isSome := by
  induction it, matched, current, next using captureNext.go.induct' HistoryStrategy nfa wf with
  | not_found it matched current next atEnd =>
    rw [captureNext.go_not_found atEnd] at h
    simpa [←h] using isSome
  | found it matched current next atEnd empty isSome' =>
    rw [captureNext.go_found atEnd empty isSome] at h
    simpa [←h] using isSome
  | ind_not_found it matched current next stepped expanded atEnd isNone₁ isNone₂ ih =>
    simp [isNone₁] at isSome
  | ind_found it matched current next stepped atEnd hemp isSome' ih =>
    rw [captureNext.go_ind_found stepped rfl atEnd hemp isSome'] at h
    have isSome' : (stepped.1 <|> matched).isSome := by
      match h : stepped.1 with
      | .some _ => simp
      | .none => simp [isSome]
    exact ih h isSome'

theorem captureNext.go.ne_done_of_path_of_none {nfa wf it₀ it matched current next} (h : captureNext.go HistoryStrategy nfa wf it matched current next = .none)
  (eqs : it.toString = it₀.toString) (v : it.Valid) (isEmpty : next.states.isEmpty)
  (ndinv : current.NotDoneInv HistoryStrategy nfa) (mopInv : current.MemOfPathInv nfa wf it₀ it)
  (inv : NeDoneOfPathInv nfa wf it₀ it) :
  ∀ it' state update, nfa.VMPath wf it₀ it' state update → nfa[state] ≠ .done := by
  induction it, matched, current, next using captureNext.go.induct' HistoryStrategy nfa wf with
  | not_found it matched current next atEnd =>
    intro it' state update path hn
    have le : it'.pos ≤ it'.toString.endPos := path.valid.le_endPos
    rw [path.toString, ←eqs] at le
    have eq : it.pos = it.toString.endPos := by
      have ⟨l, r, vf⟩ := v.validFor
      have eqr : r = [] := vf.atEnd.mp atEnd
      rw [eqr] at vf
      simp [vf.pos, vf.toString]
    exact inv it' state update (eq ▸ le) path hn
  | found it matched current next atEnd empty isSome =>
    rw [captureNext.go_found atEnd empty isSome] at h
    simp [h] at isSome
  | ind_not_found it matched current next stepped expanded atEnd isNone₁ isNone₂ ih =>
    rw [captureNext.go_ind_not_found stepped expanded rfl rfl atEnd isNone₁ isNone₂] at h
    have isNone₃ : expanded.1 = .none := by
      match h' : expanded.1 with
      | .none => rfl
      | .some _ =>
        have := some_of_some .none h (by simp [h'])
        simp at this
    have eqs' : it.next.toString = it₀.toString := by rw [it.next_toString, eqs]
    have v' : it.next.Valid := v.next' atEnd
    have isEmpty' : current.states.clear.isEmpty := by simp
    have ndinv' : expanded.2.NotDoneInv HistoryStrategy nfa :=
      ndinv.preserves stepped expanded rfl rfl isNone₂ isNone₃ (.of_empty isEmpty)
    have mopInv' : expanded.2.MemOfPathInv nfa wf it₀ it.next :=
      mopInv.preserves stepped expanded rfl rfl isNone₂ v ndinv (.of_empty isEmpty)
    have inv' : NeDoneOfPathInv nfa wf it₀ it.next := inv.preserves eqs v ndinv' mopInv'
    exact ih h eqs' v' isEmpty' ndinv' mopInv' inv'
  | ind_found it matched current next stepped atEnd hemp isSome ih =>
    rw [captureNext.go_ind_found stepped rfl atEnd hemp isSome] at h
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
theorem captureNext.ne_done_of_path_of_none {nfa wf it} (h : captureNext HistoryStrategy nfa wf it = .none)
  (v : it.Valid) :
  ∀ it' state update, nfa.VMPath wf it it' state update → nfa[state] ≠ .done := by
  simp [captureNext] at h
  set result := εClosure HistoryStrategy nfa wf it .none ⟨.empty, Vector.mkVector nfa.nodes.size HistoryStrategy.empty⟩ [(HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩)]
  match h' : result.1 with
  | .none =>
    have ndinv : SearchState.NotDoneInv HistoryStrategy nfa result.2 := εClosure.not_done_of_none result rfl h' (.of_empty (by simp))
    have mopInv : SearchState.MemOfPathInv nfa wf it it result.2 := by
      intro i update path
      have cls := path.εClosure_of_eq_it
      exact εClosure.mem_next (matched' := result.1) (next' := result.2) rfl (.of_empty (by simp)) cls
    have inv : NeDoneOfPathInv nfa wf it it := by
      intro it' state update le path
      have eqp : it'.pos = it.pos := by simpa [Pos.ext_iff] using Nat.le_antisymm le path.le_pos
      have eq : it' = it := Iterator.ext path.toString eqp
      have mem : state ∈ result.2.states := mopInv state update (eq ▸ path)
      exact ndinv state mem
    exact captureNext.go.ne_done_of_path_of_none h rfl v (by simp) ndinv mopInv inv
  | .some _ =>
    have := captureNext.go.some_of_some .none h (by simp [h'])
    simp at this

end Regex.VM
