import RegexCorrectness.NFA.Semantics.Equivalence
import RegexCorrectness.VM.Search.Lemmas

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.NFA (EquivUpdate)
open String (Pos Iterator)

namespace Regex.VM

theorem captures_of_captureNext_some {e nfa it₀ matched'} (eq : NFA.compile e = nfa)
  (h : captureNext HistoryStrategy nfa (eq ▸ NFA.compile_wf) it₀ = matched') (v : it₀.Valid) (isSome' : matched'.isSome) :
  ∃ it it' groups,
    it.toString = it₀.toString ∧
    it₀.pos ≤ it.pos ∧
    e.Captures it it' groups ∧
    EquivUpdate groups (matched'.get isSome') := by
  have ⟨state, it', hn, path⟩ := captureNext.path_done_of_matched h v isSome'
  have eq_zero := (NFA.done_iff_zero_compile eq state).mp hn
  have : state.val ≠ nfa.start := by
    simp [eq_zero]
    have : 0 < nfa.start := NFA.lt_zero_start_compile eq
    exact Nat.ne_of_lt this
  have ⟨it, eqs, le, path⟩ := path.nfaPath_of_ne this
  simp [eq_zero] at path
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile eq (path.compile_liftBound eq)
  exact ⟨it, it', groups, eqs, le, c, eqv⟩

end Regex.VM
