import RegexCorrectness.Data.BoundedIterator
import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.NFA.Semantics

set_option autoImplicit false

open String (Pos)
open Regex.NFA (EquivUpdate)
open Regex.Data (BitMatrix BoundedIterator)

namespace Regex.Backtracker

theorem captureNext.path_done_of_some {nfa wf it update} (hres : captureNext HistoryStrategy nfa wf it = .some update) (v : it.Valid) :
  ∃ state it' it'', it''.toString = it.toString ∧ nfa[state] = .done ∧ Path nfa wf it' it'' state update := by
  if le : it.pos ≤ it.toString.endPos then
    simp [captureNext_le le] at hres
    exact captureNext.go.path_done_of_some (BoundedIterator.valid_of_it_valid v) hres
  else
    simp [captureNext_not_le le] at hres

theorem captureNext.capture_of_some_compile {e it update} (hres : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it = .some update) (v : it.Valid) :
  ∃ it' it'' groups,
    it''.toString = it.toString ∧
    e.Captures it' it'' groups ∧
    EquivUpdate groups update := by
  have ⟨state, it, it', eqstring, hn, path⟩ := captureNext.path_done_of_some hres v
  have eq_zero := (NFA.done_iff_zero_compile rfl state).mp hn
  have ne : state.val ≠ (NFA.compile e).start := eq_zero ▸ Nat.ne_of_lt (NFA.lt_zero_start_compile rfl)
  have path := path.nfaPath_of_ne ne
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile rfl (eq_zero ▸ path.compile_liftBound rfl)
  exact ⟨it, it', groups, eqstring, c, eqv⟩

end Regex.Backtracker
