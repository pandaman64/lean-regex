module

public import Regex.NFA.Compile.Basic
import all Regex.NFA.Compile.Basic

public section

namespace Regex.NFA

@[grind! .]
theorem pushRegex_size_lt {nfa : NFA} {next e} :
  nfa.size < (nfa.pushRegex next e).size := by
  fun_induction pushRegex
  -- star
  case case9 nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    calc nfa.size
      _ < placeholder.size := by grind
      _ < compiled.size := ih
      _ < quest.size := by grind
      _ = _ := by grind
  all_goals grind

@[grind! .]
theorem pushRegex_wf {nfa : NFA} {next e} (wf : nfa.WellFormed) (next_lt : next < nfa.size) :
  (nfa.pushRegex next e).WellFormed := by
  fun_induction pushRegex
  -- star
  case case9 nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    have lt₁ : compiled.start < quest.size := by grind
    have lt₂ : next < quest.size := by grind
    have wfCompiled : compiled.WellFormed := ih (pushNode_wf wf (by grind)) (by grind)
    have wfQuest : quest.WellFormed := pushNode_wf wfCompiled (by grind)
    refine WellFormed.iff.mpr ⟨by grind [wfQuest.size_lt], ?_⟩
    intro i h
    if eq : i = patchAt then
      grind
    else
      grind [wfQuest.inBounds i (by grind)]
  all_goals grind

theorem compile_wf {e} : (compile e).WellFormed :=
  pushRegex_wf done_WellFormed done_WellFormed.size_lt

@[grind =]
theorem pushRegex_get_lt {nfa next e} (i : Nat) (h : i < nfa.size) :
  (pushRegex nfa next e)[i]'(Nat.lt_trans h pushRegex_size_lt) = nfa[i] := by
  fun_induction pushRegex nfa next e
  -- star
  case case9 nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    have eq : pushRegex nfa next (.star greedy e) = patched := rfl
    simp only [eq]
    conv =>
      lhs
      rw [get_eq_nodes_get, Array.getElem_setIfInBounds_ne (by grind) (by grind)]
      rw [←get_eq_nodes_get, pushNode_get_lt i (by grind), ih (by grind), pushNode_get_lt i (by grind)]
  all_goals grind

end Regex.NFA

end
