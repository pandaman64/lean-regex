import RegexCorrectness.VM.Search
import RegexCorrectness.VM.Correspondence.Materialize
import RegexCorrectness.VM.Correspondence.Refinement

set_option autoImplicit false

open Regex.Data (Span)
open Regex (NFA)
open Regex.NFA (EquivMaterializedUpdate materializeRegexGroups materializeUpdates)

namespace Regex.VM

theorem captureNext_correct {e nfa wf bufferSize it matched}
  (eq : NFA.compile e = nfa) (disj : e.Disjoint)
  (h : captureNext nfa wf bufferSize it = matched) (v : it.Valid) (isSome : matched.isSome) :
  ∃ l m r groups,
    e.Captures ⟨l, [], m ++ r⟩ ⟨l, m.reverse, r⟩ groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) (matched.get isSome) := by
  generalize h' : captureNext' nfa wf it = matched'
  have refMatched : refineUpdateOpt matched' matched := h' ▸ h ▸ captureNext'.refines
  have isSome' := (refineUpdateOpt.isSome_iff refMatched).mpr isSome
  have ⟨l, r, span, groups, eqv, c⟩ := captures_of_captureNext'_some eq h' v isSome'
  have ⟨m, eql, eqm, eqr⟩ := c.span_eq
  simp at eql eqm eqr
  subst r
  have eqspan : span = ⟨l, m.reverse, span.r⟩ :=
    calc
      _ = (⟨span.l, span.m, span.r⟩ : Span) := rfl
      _ = ⟨l, m.reverse, span.r⟩ := by simp [eql, eqm]
  have eqv' : EquivMaterializedUpdate (materializeRegexGroups groups) (materializeUpdates bufferSize (matched'.get isSome')) :=
    eqv.materialize c disj
  have eq : matched = .some (matched.get isSome) := by simp
  have eq' : matched' = .some (matched'.get isSome') := by simp
  rw [eq, eq', refineUpdateOpt] at refMatched
  exact ⟨l, m, span.r, groups, eqspan ▸ c, refMatched ▸ eqv'⟩

end Regex.VM
