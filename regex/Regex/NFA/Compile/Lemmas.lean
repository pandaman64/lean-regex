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
  case case9 nfa next greedy e patchAt placeholder compiled split quest ih =>
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
  case case9 nfa next greedy e patchAt placeholder compiled split quest ih =>
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

end Regex.NFA

end
