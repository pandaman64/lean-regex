import RegexCorrectness.NFA.Semantics.Equivalence
import RegexCorrectness.VM.Search.Lemmas

set_option autoImplicit false

open Regex.Data (SparseSet CaptureGroups)
open Regex (NFA)
open Regex.NFA (EquivUpdate)
open String (ValidPos)

namespace Regex.VM

namespace captureNext

theorem captures_of_some_compile {s e pos₀ matched'} (h : captureNext (HistoryStrategy s) (NFA.compile e) NFA.compile_wf pos₀ = matched')
  (isSome' : matched'.isSome) :
  ∃ pos pos' groups,
    pos₀ ≤ pos ∧
    e.Captures pos pos' groups ∧
    EquivUpdate groups (matched'.get isSome') := by
  have ⟨state, pos', hn, path⟩ := path_done_of_matched h isSome'
  have eq_zero := (NFA.done_iff_zero_compile rfl state).mp hn
  have : state.val ≠ (NFA.compile e).start := by
    simp [eq_zero]
    exact Nat.ne_of_lt (NFA.lt_zero_start_compile rfl)
  have ⟨pos, le, path⟩ := path.nfaPath_of_ne this
  simp [eq_zero] at path
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile rfl (path.compile_liftBound rfl)
  exact ⟨pos, pos', groups, le, c, eqv⟩

theorem not_captures_of_none_compile {s e pos} (h : captureNext (HistoryStrategy s) (NFA.compile e) NFA.compile_wf pos = .none)
  (pos' pos'' : ValidPos s) (groups : CaptureGroups s) (le : pos ≤ pos') :
  ¬e.Captures pos' pos'' groups := by
  intro c
  let zero : Fin (NFA.compile e).nodes.size := ⟨0, NFA.lt_zero_size_compile rfl⟩
  have ⟨update, _, path⟩ := NFA.path_of_captures_compile rfl c
  have path := NFA.VMPath.of_nfaPath NFA.compile_wf le (path.liftBound (by decide))
  have ne := ne_done_of_path_of_none h pos'' zero update path
  exact ne ((NFA.done_iff_zero_compile rfl zero).mpr rfl)

end captureNext

end Regex.VM
