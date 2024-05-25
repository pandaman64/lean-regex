-- Correctness of the NFA compilation
import RegexCorrectness.NFA.Transition

namespace NFA

theorem evalFrom_of_compile_matches (eq : NFA.compile r = nfa) (m : r.matches ⟨cs⟩) :
  0 ∈ nfa.evalFrom {nfa.start.val} cs := by
  unfold compile at eq
  have ev := evalFrom_of_matches (rfl : NFA.done.pushRegex ⟨0, by decide⟩ r = _) m _ le_refl
  exact eq ▸ ev

theorem matches_of_compile_evalFrom (eq : NFA.compile r = nfa) (ev : 0 ∈ nfa.evalFrom {nfa.start.val} cs) :
  r.matches ⟨cs⟩ := by
  have path := pathIn_of_evalFrom ev
  have path := pathToNext_of_compile_of_pathIn eq path
  exact matches_prefix_of_compile eq path

end NFA
