import RegexCorrectness.Data.BVPos
import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.NFA.Semantics

set_option autoImplicit false

open String (Pos Iterator)
open Regex.NFA (EquivUpdate)
open Regex.Data (CaptureGroups BitMatrix BoundedIterator)

namespace Regex.Backtracker

namespace captureNext

theorem path_done_of_some {nfa wf it update} (hres : captureNext HistoryStrategy nfa wf it = .some update) (v : it.Valid) :
  ∃ state it' it'', nfa[state] = .done ∧ it'.toString = it.toString ∧ it.pos ≤ it'.pos ∧ Path nfa wf it' it'' state update := by
  let bit : BoundedIterator it.pos.byteIdx it.toString.endPos.byteIdx := ⟨it, Nat.le_refl _, v.le_endPos, rfl⟩
  simp [captureNext_le v.le_endPos] at hres
  have ⟨state, bit', bit'', hn, reaches, path⟩ := go.path_done_of_some (bit := bit) v hres
  have ⟨_, _, eqs, le⟩ := BoundedIterator.Reaches.iff_valid_le_pos.mp reaches
  simp [BoundedIterator.toString] at eqs
  simp [BoundedIterator.pos] at le
  exact ⟨state, bit'.it, bit''.it, hn, eqs.symm, le, path⟩

theorem capture_of_some_compile {e it update} (hres : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it = .some update) (v : it.Valid) :
  ∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    e.Captures it' it'' groups ∧
    EquivUpdate groups update := by
  have ⟨state, it', it'', hn, eqs, le, path⟩ := path_done_of_some hres v
  have eq_zero := (NFA.done_iff_zero_compile rfl state).mp hn
  have ne : state.val ≠ (NFA.compile e).start := eq_zero ▸ Nat.ne_of_lt (NFA.lt_zero_start_compile rfl)
  have path := path.nfaPath_of_ne ne
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile rfl (eq_zero ▸ path.compile_liftBound rfl)
  exact ⟨it', it'', groups, eqs, le, c, eqv⟩

theorem ne_done_of_path_of_none {nfa wf it} (hres : captureNext HistoryStrategy nfa wf it = .none) (v : it.Valid) :
  ∀ (it' it'' : Iterator) (state : Fin nfa.nodes.size) (update : List (Nat × Pos.Raw)),
    it'.toString = it.toString →
    it.pos ≤ it'.pos →
    Path nfa wf it' it'' state update →
    nfa[state] ≠ .done := by
  simp [captureNext_le v.le_endPos] at hres

  let startIdx := it.pos.byteIdx
  let maxIdx := it.toString.endPos.byteIdx
  let bit : BoundedIterator startIdx maxIdx := ⟨it, Nat.le_refl _, v.le_endPos, rfl⟩
  let visited := BitMatrix.zero nfa.nodes.size (maxIdx + 1 - startIdx)

  have reaches : bit.Reaches bit := .refl v
  have h := go.ne_done_of_path_of_none hres reaches go.Inv.zero captureNextAux.NotDoneInv.zero

  intro it' it'' state update eqs ge path hn
  have v' : it'.Valid := path.validL
  have v'' : it''.Valid := path.validR
  have le' : it'.pos ≤ it.toString.endPos := eqs ▸ v'.le_endPos
  have le'' : it''.pos ≤ it.toString.endPos := eqs ▸ path.toString_eq ▸ v''.le_endPos
  let bit' : BoundedIterator startIdx maxIdx := ⟨it', ge, le', eqs ▸ rfl⟩
  let bit'' : BoundedIterator startIdx maxIdx := ⟨it'', Nat.le_trans ge path.le_pos, le'', path.toString_eq ▸ eqs ▸ rfl⟩

  have reaches : bit.Reaches bit' := by
    simp [BoundedIterator.Reaches.iff_valid_le_pos]
    exact ⟨v, v', eqs.symm, ge⟩

  exact h bit' bit'' state update reaches path hn

theorem not_captures_of_none_compile {e it} (hres : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it = .none) (v : it.Valid)
  (it' it'' : Iterator) (groups : CaptureGroups) (eqs : it'.toString = it.toString) (le : it.pos ≤ it'.pos) :
  ¬e.Captures it' it'' groups := by
  intro c
  have ⟨update, _, path⟩ := NFA.path_of_captures_compile rfl c

  let zero : Fin (NFA.compile e).nodes.size := ⟨0, NFA.lt_zero_size_compile rfl⟩
  have hne := ne_done_of_path_of_none hres v it' it'' zero update eqs le (Path.of_nfaPath (path.liftBound (by decide)))
  have hn := (NFA.done_iff_zero_compile (e := e) rfl zero).mpr (by simp [zero])
  exact hne hn

end captureNext

end Regex.Backtracker
