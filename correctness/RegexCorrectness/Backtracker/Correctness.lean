import RegexCorrectness.Backtracker.Compile
import RegexCorrectness.Backtracker.Refinement

set_option autoImplicit false

open Regex.Data (Span)
open Regex (NFA)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates refineUpdateOpt refineUpdate)

namespace Regex.Backtracker

theorem captureNext_correct {e bufferSize it matchedB}
  (disj : e.Disjoint)
  (hresB : captureNext (BufferStrategy bufferSize) (NFA.compile e) NFA.compile_wf it = .some matchedB) (v : it.Valid) :
  ∃ it' it'' groups,
    it''.toString = it.toString ∧
    e.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matchedB := by
  match hresH : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it with
  | .some matchedH =>
    have ref := hresH ▸ hresB ▸ captureNext.refines (NFA.compile e) NFA.compile_wf bufferSize it
    simp [refineUpdateOpt, refineUpdate] at ref
    have ⟨it', it'', groups, eqstring, c, eqv⟩ := captureNext.capture_of_some_compile hresH v
    exact ⟨it', it'', groups, eqstring, c, ref ▸ eqv.materialize c disj⟩
  | .none =>
    have := hresH ▸ hresB ▸ captureNext.refines (NFA.compile e) NFA.compile_wf bufferSize it
    simp [refineUpdateOpt] at this

end Regex.Backtracker
