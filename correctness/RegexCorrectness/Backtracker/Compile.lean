import RegexCorrectness.Data.BVPos
import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.NFA.Semantics

set_option autoImplicit false

open String (Pos)
open Regex.NFA (EquivUpdate)
open Regex.Data (CaptureGroups BitMatrix BVPos)

namespace Regex.Backtracker

namespace captureNext

theorem path_done_of_some {s nfa wf pos update} (hres : captureNext (HistoryStrategy s) nfa wf pos = .some update) :
  ∃ state pos' pos'', nfa[state] = .done ∧ pos ≤ pos' ∧ Path nfa wf pos' pos'' state update := by
  let bvpos : BVPos pos := ⟨pos, Pos.le_refl _⟩
  dsimp [captureNext] at hres
  have ⟨state, bvpos', bvpos'', hn, le, path⟩ := go.path_done_of_some hres
  exact ⟨state, bvpos'.current, bvpos''.current, hn, le, path⟩

theorem capture_of_some_compile {s e pos update} (hres : captureNext (HistoryStrategy s) (NFA.compile e) NFA.compile_wf pos = .some update) :
  ∃ pos' pos'' groups,
    pos ≤ pos' ∧
    e.Captures pos' pos'' groups ∧
    EquivUpdate groups update := by
  have ⟨state, pos', pos'', hn, le, path⟩ := path_done_of_some hres
  have eq_zero := (NFA.done_iff_zero_compile rfl state).mp hn
  have ne : state.val ≠ (NFA.compile e).start := eq_zero ▸ Nat.ne_of_lt (NFA.lt_zero_start_compile rfl)
  have path := path.nfaPath_of_ne ne
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile rfl (eq_zero ▸ path.compile_liftBound rfl)
  exact ⟨pos', pos'', groups, le, c, eqv⟩

theorem ne_done_of_path_of_none {s nfa wf pos} (hres : captureNext (HistoryStrategy s) nfa wf pos = .none) :
  ∀ (pos' pos'' : Pos s) (state : Fin nfa.nodes.size) (update : List (Nat × Pos s)),
    pos ≤ pos' →
    Path nfa wf pos' pos'' state update →
    nfa[state] ≠ .done := by
  dsimp [captureNext] at hres

  let bvpos : BVPos pos := ⟨pos, Pos.le_refl _⟩
  let visited := BitMatrix.zero nfa.nodes.size (pos.remainingBytes + 1)

  have h := go.ne_done_of_path_of_none hres (BVPos.le_refl _) go.Inv.zero captureNextAux.NotDoneInv.zero

  intro pos' pos'' state update le path hn
  let bvpos' : BVPos pos := ⟨pos', le⟩
  let bvpos'' : BVPos pos := ⟨pos'', Pos.le_trans le path.le⟩

  exact h bvpos' bvpos'' state update bvpos'.le path hn

theorem not_captures_of_none_compile {s e pos} (hres : captureNext (HistoryStrategy s) (NFA.compile e) NFA.compile_wf pos = .none)
  (pos' pos'' : Pos s) (groups : CaptureGroups s) (le : pos ≤ pos') :
  ¬e.Captures pos' pos'' groups := by
  intro c
  have ⟨update, _, path⟩ := NFA.path_of_captures_compile rfl c

  let zero : Fin (NFA.compile e).nodes.size := ⟨0, NFA.lt_zero_size_compile rfl⟩
  have hne := ne_done_of_path_of_none hres pos' pos'' zero update le (Path.of_nfaPath (path.liftBound (by decide)))
  have hn := (NFA.done_iff_zero_compile (e := e) rfl zero).mpr (by simp [zero])
  exact hne hn

end captureNext

end Regex.Backtracker
