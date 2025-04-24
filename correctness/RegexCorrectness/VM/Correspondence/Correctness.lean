import RegexCorrectness.VM.Search
import RegexCorrectness.VM.Correspondence.Refinement

set_option autoImplicit false

open Regex.Data (Span)
open Regex (NFA)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates refineUpdateOpt)

namespace Regex.VM

theorem captureNext_correct {e nfa wf bufferSize it matched}
  (eq : NFA.compile e = nfa) (disj : e.Disjoint)
  (h : captureNext (BufferStrategy bufferSize) nfa wf it = matched) (v : it.Valid) (isSome : matched.isSome) :
  ∃ it' it'' groups,
    it''.toString = it.toString ∧
    e.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) (matched.get isSome) := by
  generalize h' : captureNext HistoryStrategy nfa wf it = matched'
  have refMatched : refineUpdateOpt matched' matched := h' ▸ h ▸ captureNext.refines
  have isSome' := (refineUpdateOpt.isSome_iff refMatched).mpr isSome
  have ⟨it', it'', groups, eqstring, c, eqv⟩ := captures_of_captureNext_some eq h' v isSome'
  have eqv' : EquivMaterializedUpdate (materializeRegexGroups groups) (materializeUpdates bufferSize (matched'.get isSome')) :=
    eqv.materialize c disj
  have eq : matched = .some (matched.get isSome) := by simp
  have eq' : matched' = .some (matched'.get isSome') := by simp
  rw [eq, eq', refineUpdateOpt] at refMatched
  exact ⟨it', it'', groups, eqstring, c, refMatched ▸ eqv'⟩

end Regex.VM
