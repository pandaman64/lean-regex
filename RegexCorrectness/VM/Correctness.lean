import RegexCorrectness.VM.Basic

open Regex.NFA

namespace Regex.VM

theorem matches_of_captureNext
  (eq : compile re = nfa)
  (h : captureNext nfa wf it saveSize = matched)
  (v : it.Valid)
  (hsome : matched.isSome) :
  ∃ (s : Substring) (l m r : List Char),
    s.ValidFor l m r ∧ it.toString = ⟨l ++ m ++ r⟩ ∧ re.matches m := by
  have ⟨s, l, m, r, sv, eqs, i, hr, hdone⟩ := captureNext_spec h v hsome
  have ma := matches_of_reaches eq hr hdone
  exact ⟨s, l, m, r, sv, eqs, ma⟩

end Regex.VM
