import RegexCorrectness.VM.Search
import RegexCorrectness.VM.Correspondence.Refinement
import RegexCorrectness.Spec

set_option autoImplicit false

open Regex (NFA)
open Regex.Data (Expr CaptureGroups)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates)
open RegexCorrectness.Spec (SearchProblem)
open String (Iterator)

namespace Regex.VM

theorem captureNext_soundness {e bufferSize it matchedB}
  (disj : e.Disjoint)
  (hresB : captureNext (BufferStrategy bufferSize) (NFA.compile e) NFA.compile_wf it = .some matchedB) (v : it.Valid) :
  ∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    e.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matchedB := by
  match hresH : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it with
  | .some matchedH =>
    have refResult := hresH ▸ hresB ▸ captureNext.refines
    simp [materializeUpdates] at refResult
    have ⟨it', it'', groups, eqs, le, c, eqv⟩ := captureNext.captures_of_some_compile hresH v (by simp)
    have eqv' : EquivMaterializedUpdate (materializeRegexGroups groups) (materializeUpdates bufferSize matchedH) :=
      eqv.materialize c disj
    exact ⟨it', it'', groups, eqs, le, c, refResult ▸ eqv'⟩
  | .none =>
    have refResult := hresH ▸ hresB ▸ captureNext.refines
    simp at refResult

theorem captureNext_completeness' {e bufferSize it}
  (hresB : captureNext (BufferStrategy bufferSize) (NFA.compile e) NFA.compile_wf it = .none) (v : it.Valid)
  (it' it'' : Iterator) (groups : CaptureGroups) (eqs : it'.toString = it.toString) (le : it.pos ≤ it'.pos) (c : e.Captures it' it'' groups) :
  False := by
  match hresH : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it with
  | .some matchedH =>
    have refResult := hresH ▸ hresB ▸ captureNext.refines
    simp at refResult
  | .none => exact captureNext.not_captures_of_none_compile hresH v it' it'' groups eqs le c

theorem captureNext_completeness {e bufferSize it}
  (hresB : captureNext (BufferStrategy bufferSize) (NFA.compile e) NFA.compile_wf it = .none) (v : it.Valid) :
  ¬∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    e.Captures it' it'' groups := by
  grind [captureNext_completeness']

-- NOTE: we don't make this an instance because there are multiple decision procedures
def decideSearchProblem (e : Expr) (it : Iterator) (disj : e.Disjoint) (v : it.Valid) : Decidable (SearchProblem e it) :=
  match hresB : captureNext (BufferStrategy 0) (NFA.compile e) NFA.compile_wf it with
  | .some _ => .isTrue <|
    have ⟨it', it'', groups, eqs, le, c, _⟩ := captureNext_soundness disj hresB v
    ⟨it', it'', groups, eqs, le, c⟩
  | .none => .isFalse (captureNext_completeness hresB v)

end Regex.VM
