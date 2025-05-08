import RegexCorrectness.NFA.Semantics.Equivalence
import RegexCorrectness.VM.Search.Lemmas

set_option autoImplicit false

open Regex.Data (SparseSet CaptureGroups)
open Regex (NFA)
open Regex.NFA (EquivUpdate)
open String (Pos Iterator)

namespace Regex.VM

namespace captureNext

theorem captures_of_some_compile {e it₀ matched'} (h : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it₀ = matched')
  (v : it₀.Valid) (isSome' : matched'.isSome) :
  ∃ it it' groups,
    it.toString = it₀.toString ∧
    it₀.pos ≤ it.pos ∧
    e.Captures it it' groups ∧
    EquivUpdate groups (matched'.get isSome') := by
  have ⟨state, it', hn, path⟩ := path_done_of_matched h v isSome'
  have eq_zero := (NFA.done_iff_zero_compile rfl state).mp hn
  have : state.val ≠ (NFA.compile e).start := by
    simp [eq_zero]
    exact Nat.ne_of_lt (NFA.lt_zero_start_compile rfl)
  have ⟨it, eqs, le, path⟩ := path.nfaPath_of_ne this
  simp [eq_zero] at path
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile rfl (path.compile_liftBound rfl)
  exact ⟨it, it', groups, eqs, le, c, eqv⟩

theorem not_captures_of_none_compile {e it} (h : captureNext HistoryStrategy (NFA.compile e) NFA.compile_wf it = .none) (v : it.Valid)
  (it' it'' : Iterator) (groups : CaptureGroups) (eqs : it'.toString = it.toString) (le : it.pos ≤ it'.pos) :
  ¬e.Captures it' it'' groups := by
  intro c
  let zero : Fin (NFA.compile e).nodes.size := ⟨0, NFA.lt_zero_size_compile rfl⟩
  have ⟨update, _, path⟩ := NFA.path_of_captures_compile rfl c
  have path := NFA.VMPath.of_nfaPath NFA.compile_wf eqs le (path.liftBound (by decide))
  have ne := ne_done_of_path_of_none h v it'' zero update path
  exact ne ((NFA.done_iff_zero_compile rfl zero).mpr rfl)

end captureNext

end Regex.VM
