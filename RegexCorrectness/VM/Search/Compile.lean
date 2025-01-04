import RegexCorrectness.NFA.Semantics.Equivalence
import RegexCorrectness.VM.Search.Lemmas

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open Regex.NFA (EquivUpdate)
open String (Pos Iterator)

namespace Regex.VM

theorem captures_of_captureNext'_some {e nfa it matched'} (eq : NFA.compile e = nfa)
  (h : captureNext' nfa (eq ▸ NFA.compile_wf) it = matched') (v : it.Valid) (isSome' : matched'.isSome) :
  ∃ l r span groups,
    span.toString = it.toString ∧
    e.Captures ⟨l, [], r⟩ span groups ∧
    EquivUpdate groups (matched'.get isSome') := by
  have ⟨state, span, eqstring, hn, path⟩ := captureNext'.path_done_of_matched h v isSome'
  have eq_zero := (NFA.done_iff_zero_compile eq state).mp hn
  have : state.val ≠ nfa.start := by
    simp [eq_zero]
    have : 0 < nfa.start := NFA.lt_zero_start_compile eq
    exact Nat.ne_of_lt this
  have ⟨l, r, path⟩ := path.nfaPath_of_ne this
  simp [eq_zero] at path
  have ⟨groups, eqv, c⟩ := NFA.captures_of_path_compile eq (path.compile_liftBound eq)
  exact ⟨l, r, span, groups, eqstring, c, eqv⟩

end Regex.VM
