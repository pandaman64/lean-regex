import RegexCorrectness.VM.Search.Basic

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

-- TODO: state that the path starts at a position between `it₀` and `it`.
def MatchedInv (nfa : NFA) (wf : nfa.WellFormed) (it₀ : Iterator) (matched : Option (List (Nat × Pos))) : Prop :=
  (isSome : matched.isSome) →
    ∃ state it,
      it.toString = it₀.toString ∧
      nfa[state] = .done ∧
      nfa.VMPath wf it state (matched.get isSome)

theorem captureNext.go.inv {nfa wf it₀ it matched current next matched'}
  (h : captureNext.go HistoryStrategy nfa wf it matched current next = matched')
  (v : it.Valid) (string_eq : it.toString = it₀.toString)
  (curr_inv : current.Inv nfa wf it) (empty : next.states.isEmpty)
  (matched_inv : MatchedInv nfa wf it₀ matched) :
  MatchedInv nfa wf it₀ matched' := by
  induction it, matched, current, next using captureNext.go.induct' HistoryStrategy nfa wf with
  | not_found it matched current next atEnd => simp_all
  | found it matched current next atEnd empty' some =>
    rw [captureNext.go_found atEnd empty' some] at h
    simp_all
  | ind_not_found it matched current next _ current' matched'' next' atEnd isNone h₁ h₂ ih =>
    rw [captureNext.go_ind_not_found atEnd isNone h₁ h₂] at h
    have curr'_inv := εClosure.inv_of_inv h₁ v curr_inv
    have next'_inv := eachStepChar.inv_of_inv h₂ v atEnd empty curr'_inv
    have matched''_inv : MatchedInv nfa wf it₀ matched'' := by
      intro isSome''
      have ⟨state', mem', hn, hupdate⟩ := eachStepChar.done_of_matched_some h₂ isSome''
      have ⟨update, path, write⟩ := next'_inv state' mem'
      simp [εClosure.writeUpdate, hn] at write
      simp at hupdate
      simp [←write, hupdate] at path
      exact ⟨state', it.next, by rw [it.next_toString, string_eq], hn, path⟩
    exact ih h (v.next (it.hasNext_of_not_atEnd atEnd)) string_eq next'_inv (by simp) matched''_inv
  | ind_found it matched current next matched'' next' atEnd empty' isSome h' ih =>
    rw [captureNext.go_ind_found atEnd empty' isSome h'] at h
    have next'_inv := eachStepChar.inv_of_inv h' v atEnd empty curr_inv
    have matched''_inv : MatchedInv nfa wf it₀ (matched'' <|> matched) := by
      cases matched'' with
      | none => simp [matched_inv]
      | some matched'' =>
        simp
        have ⟨state', mem', hn, hupdate⟩ := eachStepChar.done_of_matched_some h' (by simp)
        have ⟨update, path, write⟩ := next'_inv state' mem'
        simp [εClosure.writeUpdate, hn] at write
        simp at hupdate
        simp [←write, hupdate] at path
        intro _
        exact ⟨state', it.next, by rw [it.next_toString, string_eq], hn, path⟩
    exact ih h (v.next (it.hasNext_of_not_atEnd atEnd)) string_eq next'_inv (by simp) matched''_inv

/--
If `captureNext` returns `some`, the returned list corresponds to the updates of a path from
`nfa.start` to a `.done` state.
-/
theorem captureNext.path_done_of_matched {nfa wf it₀ matched'}
  (h : captureNext HistoryStrategy nfa wf it₀ = matched') (v : it₀.Valid) (isSome' : matched'.isSome) :
  ∃ state it,
    it.toString = it₀.toString ∧
    nfa[state] = .done ∧
    nfa.VMPath wf it state (matched'.get isSome') := by
  simp [captureNext] at h

  set result := εClosure HistoryStrategy nfa wf it₀ .none ⟨.empty, Vector.mkVector nfa.nodes.size []⟩ [([], ⟨nfa.start, wf.start_lt⟩)]
  set matched := result.1
  set current := result.2
  have h' : result = (matched, current) := rfl
  have curr_inv : current.Inv nfa wf it₀ := εClosure.inv_of_inv h' v (.of_empty (by simp))
  have matched_inv : MatchedInv nfa wf it₀ matched := by
    intro isSome
    have ⟨state, mem, hn, hupdate⟩ := εClosure.matched_inv h' (by simp) isSome
    have ⟨update, path, write⟩ := curr_inv state mem
    simp [εClosure.writeUpdate, hn, hupdate] at write
    exact ⟨state, it₀, rfl, hn, write ▸ path⟩

  exact captureNext.go.inv h v rfl curr_inv (by simp) matched_inv isSome'

end Regex.VM
