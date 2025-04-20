import RegexCorrectness.Data.BoundedIterator
import RegexCorrectness.Data.Span
import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.NFA.Semantics

set_option autoImplicit false

open String (Pos)
open Regex.NFA (EquivUpdate)
open Regex.Data (BoundedIterator Span)

namespace Regex.Backtracker

theorem captureNext.go.path_done_of_some {nfa wf startIdx bit update} {visited visited' : BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx)}
  (v : bit.Valid) (hres : captureNext.go HistoryStrategy nfa wf startIdx bit visited = (.some update, visited')) :
  ∃ l r state span, span.toString = bit.it.toString ∧ nfa[state] = .done ∧ Path nfa wf l r span state update := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx with
  | found bit visited update' visited' haux =>
    simp [captureNext.go_found haux] at hres
    simp [hres] at haux
    have ⟨l, r, vf⟩ := (bit.valid_of_valid v).validFor
    have inv₀ : captureNextAux.UpperInv wf l.reverse r [⟨[], ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] := by
      refine ⟨?_⟩
      simp
      have vfs := Span.validFor ⟨l.reverse, [], r⟩
      simp at vfs
      exact ⟨⟨l.reverse, [], r⟩, vfs.eq_it vf, .init⟩
    have ⟨state, span, hn, path⟩ := captureNextAux.path_done_of_some haux inv₀
    exact ⟨l.reverse, r, state, span, by simp [path.string_eq, vf.out], hn, path⟩
  | not_found_next bit visited visited' haux hnext ih =>
    simp [captureNext.go_not_found_next haux hnext] at hres
    exact ih (bit.next_valid hnext v) hres
  | not_found_end bit visited visited' haux hnext => simp [captureNext.go_not_found_end haux hnext] at hres

theorem captureNext.path_done_of_some {nfa wf it update} (hres : captureNext HistoryStrategy nfa wf it = .some update) (v : it.Valid) :
  ∃ l r state span, span.toString = it.toString ∧ nfa[state] = .done ∧ Path nfa wf l r span state update := by
  if le : it.pos ≤ it.toString.endPos then
    simp [captureNext_le le] at hres
    let result := go HistoryStrategy nfa wf it.pos.byteIdx ⟨it, (Nat.le_refl _), le⟩ (BitMatrix.zero _ _)
    change result.1 = .some update at hres
    have : result = (.some update, result.2) := by simp [Prod.ext_iff, hres]
    exact captureNext.go.path_done_of_some (BoundedIterator.valid_of_it_valid _ v) this
  else
    simp [captureNext_not_le le] at hres

theorem captureNext.capture_of_some_compile {e it update} (hres : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it = .some update) (v : it.Valid) :
  ∃ l r span groups,
    span.toString = it.toString ∧
    e.Captures ⟨l, [], r⟩ span groups ∧
    EquivUpdate groups update := by
  have ⟨l, r, state, span, eqstring, hn, path⟩ := captureNext.path_done_of_some hres v
  have eq_zero := (NFA.done_iff_zero_compile rfl state).mp hn
  have ne : state.val ≠ (NFA.compile e).start := eq_zero ▸ Nat.ne_of_lt (NFA.lt_zero_start_compile rfl)
  have path := path.nfaPath_of_ne ne
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile rfl (eq_zero ▸ path.compile_liftBound rfl)
  exact ⟨l, r, span, groups, eqstring, c, eqv⟩

end Regex.Backtracker
