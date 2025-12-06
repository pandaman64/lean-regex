import RegexCorrectness.Backtracker.Compile
import RegexCorrectness.Backtracker.Refinement
import RegexCorrectness.Spec

set_option autoImplicit false

open Regex (NFA)
open Regex.Data (Expr CaptureGroups)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates)
open RegexCorrectness.Spec (SearchProblem)
open String (ValidPos)

namespace Regex.Backtracker

theorem captureNext_soundness {s e bufferSize pos matchedB}
  (disj : e.Disjoint)
  (hresB : captureNext (BufferStrategy s bufferSize) (NFA.compile e) NFA.compile_wf pos = .some matchedB) :
  ∃ (pos' pos'' : ValidPos s) (groups : CaptureGroups s),
    pos ≤ pos' ∧
    e.Captures pos' pos'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matchedB := by
  match hresH : captureNext (HistoryStrategy s) (NFA.compile e) NFA.compile_wf pos with
  | .some matchedH =>
    have refResult := hresH ▸ hresB ▸ captureNext.refines (NFA.compile e) NFA.compile_wf bufferSize pos
    simp [materializeResult] at refResult
    have ⟨pos', pos'', groups, le, c, eqv⟩ := captureNext.capture_of_some_compile hresH
    exact ⟨pos', pos'', groups, le, c, refResult ▸ eqv.materialize c disj⟩
  | .none =>
    have refResult := hresH ▸ hresB ▸ captureNext.refines (NFA.compile e) NFA.compile_wf bufferSize pos
    simp [materializeResult] at refResult

theorem captureNext_completeness' {s e bufferSize pos}
  (hresB : captureNext (BufferStrategy s bufferSize) (NFA.compile e) NFA.compile_wf pos = .none)
  (pos' pos'' : ValidPos s) (groups : CaptureGroups s) (le : pos ≤ pos') (c : e.Captures pos' pos'' groups) :
  False := by
  match hresH : captureNext (HistoryStrategy s) (NFA.compile e) NFA.compile_wf pos with
  | .some matchedH =>
    have refResult := hresH ▸ hresB ▸ captureNext.refines (NFA.compile e) NFA.compile_wf bufferSize pos
    simp [materializeResult] at refResult
  | .none => exact captureNext.not_captures_of_none_compile hresH pos' pos'' groups le c

theorem captureNext_completeness {s e bufferSize pos}
  (hresB : captureNext (BufferStrategy s bufferSize) (NFA.compile e) NFA.compile_wf pos = .none) :
  ¬∃ (pos' pos'' : ValidPos s) (groups : CaptureGroups s),
    pos ≤ pos' ∧
    e.Captures pos' pos'' groups := by
  grind [captureNext_completeness']

-- NOTE: we don't make this an instance because there are multiple decision procedures
def decideSearchProblem {s : String} (e : Expr) (pos : ValidPos s) (disj : e.Disjoint) : Decidable (SearchProblem e pos) :=
  match hresB : captureNext (BufferStrategy s 0) (NFA.compile e) NFA.compile_wf pos with
  | .some _ => .isTrue <|
    have ⟨pos', pos'', groups, le, c, _⟩ := captureNext_soundness disj hresB
    ⟨pos', pos'', groups, le, c⟩
  | .none => .isFalse (captureNext_completeness hresB)

end Regex.Backtracker
