import RegexCorrectness.VM.Search.Basic

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

-- TODO: state that span is before the current iterator position
def MatchedInv (nfa : NFA) (wf : nfa.WellFormed) (matched : Option (List (Nat × Pos))) : Prop :=
  (isSome : matched.isSome) → ∃ state span, nfa[state] = .done ∧ nfa.VMPath wf span state (matched.get isSome)

theorem captureNext'.go.inv {nfa wf it matched current next matched'}
  (h : captureNext'.go nfa wf it matched current next = matched')
  (v : it.Valid) (curr_inv : current.Inv nfa wf it) (empty : next.states.isEmpty)
  (matched_inv : MatchedInv nfa wf matched) :
  MatchedInv nfa wf matched' := by
  induction it, matched, current, next using captureNext'.go.induct' nfa wf with
  | not_found it matched current next atEnd => simp_all
  | found it matched current next atEnd empty' some =>
    rw [captureNext'.go_found atEnd empty' some] at h
    simp_all
  | ind_not_found it matched current next _ current' matched'' next' atEnd isNone h₁ h₂ ih =>
    rw [captureNext'.go_ind_not_found atEnd isNone h₁ h₂] at h
    have curr'_inv := εClosure.inv_of_inv h₁ v curr_inv
    have next'_inv := eachStepChar.inv_of_inv h₂ atEnd empty curr'_inv
    have matched''_inv : MatchedInv nfa wf matched'' := by
      intro isSome''
      have ⟨state', mem', hn, hupdate⟩ := eachStepChar.done_of_matched_some h₂ isSome''
      have ⟨span, update, eqit, path, write⟩ := next'_inv state' mem'
      simp [WriteUpdate, hn] at write
      simp at hupdate
      simp [←write, hupdate] at path
      exact ⟨state', span, hn, path⟩
    exact ih h (v.next (it.hasNext_of_not_atEnd atEnd)) next'_inv (by simp) matched''_inv
  | ind_found it matched current next matched'' next' atEnd empty' isSome h' ih =>
    rw [captureNext'.go_ind_found atEnd empty' isSome h'] at h
    have next'_inv := eachStepChar.inv_of_inv h' atEnd empty curr_inv
    have matched''_inv : MatchedInv nfa wf (matched'' <|> matched) := by
      cases matched'' with
      | none => simp [matched_inv]
      | some matched'' =>
        simp
        have ⟨state', mem', hn, hupdate⟩ := eachStepChar.done_of_matched_some h' (by simp)
        have ⟨span, update, eqit, path, write⟩ := next'_inv state' mem'
        simp [WriteUpdate, hn] at write
        simp at hupdate
        simp [←write, hupdate] at path
        intro _
        exact ⟨state', span, hn, path⟩
    exact ih h (v.next (it.hasNext_of_not_atEnd atEnd)) next'_inv (by simp) matched''_inv

/--
If `captureNext'` returns `some`, the returned list corresponds to the updates of a path from
`nfa.start` to a `.done` state.
-/
theorem captureNext'.path_done_of_matched {nfa wf it matched'}
  (h : captureNext' nfa wf it = matched') (v : it.Valid) (isSome' : matched'.isSome) :
  ∃ state span, nfa[state] = .done ∧ nfa.VMPath wf span state (matched'.get isSome') := by
  simp [captureNext'] at h

  set result := εClosure' nfa wf it .none ⟨.empty, Vec.ofFn (fun _ => [])⟩ [([], ⟨nfa.start, wf.start_lt⟩)]
  set matched := result.1
  set current := result.2
  have h' : result = (matched, current) := rfl
  have curr_inv : current.Inv nfa wf it := εClosure.inv_of_inv h' v (.of_empty (by simp))
  have matched_inv : MatchedInv nfa wf matched := by
    intro isSome
    have h' : result = (matched, current) := rfl
    have ⟨state, mem, hn, hupdate⟩ := εClosure.matched_inv h' (by simp) isSome
    have ⟨span, update, eqit, path, write⟩ := curr_inv state mem
    simp [WriteUpdate, hn, hupdate] at write
    exact ⟨state, span, hn, write ▸ path⟩

  exact captureNext'.go.inv h v curr_inv (by simp) matched_inv isSome'

end Regex.VM
