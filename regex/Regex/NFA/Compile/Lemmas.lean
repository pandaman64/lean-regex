import Regex.NFA.Compile.Basic

namespace Regex.NFA

theorem pushRegex_size_lt {nfa : NFA} {next e} :
  nfa.nodes.size < (nfa.pushRegex next e).nodes.size := by
  induction e generalizing nfa next with
  | empty => simp [pushRegex]
  | epsilon => simp [pushRegex]
  | anchor a => simp [pushRegex]
  | char => simp [pushRegex]
  | classes => simp [pushRegex]
  | group tag e ih =>
    simp [pushRegex]
    calc nfa.nodes.size
      _ < (nfa.pushNode (.save (2 * tag + 1) next)).nodes.size := by simp
      _ < ((nfa.pushNode (.save (2 * tag + 1) next)).pushRegex nfa.nodes.size e).nodes.size := ih
      _ < _ := by omega
  | alternate e₁ e₂ ih₁ ih₂ =>
    simp [pushRegex]
    calc nfa.nodes.size
      _ < (nfa.pushRegex next e₁).nodes.size := ih₁
      _ < ((nfa.pushRegex next e₁).pushRegex next e₂).nodes.size := ih₂
      _ < _ := by omega
  | concat e₁ e₂ ih₁ ih₂ =>
    simp [pushRegex]
    calc nfa.nodes.size
      _ < (nfa.pushRegex next e₂).nodes.size := ih₂
      _ < _ := ih₁
  | star greedy e ih =>
    simp [pushRegex]
    calc nfa.nodes.size
      _ < (nfa.pushNode .fail).nodes.size := by simp
      _ < ((nfa.pushNode .fail).pushRegex nfa.nodes.size e).nodes.size := ih

end Regex.NFA
