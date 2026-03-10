module

public import Regex.NFA.Compile.Basic
import all Regex.NFA.Compile.Basic

namespace Regex.NFA

public theorem pushRegex_size_lt {nfa : NFA} {next e} :
  nfa.size < (nfa.pushRegex next e).size := by
  induction e generalizing nfa next with
  | empty => simp [pushRegex]
  | epsilon => simp [pushRegex]
  | anchor a => simp [pushRegex]
  | char => simp [pushRegex]
  | classes => simp [pushRegex]
  | group tag e ih =>
    simp [pushRegex]
    calc nfa.size
      _ < (nfa.pushNode (.save (2 * tag + 1) next)).size := by simp
      _ < ((nfa.pushNode (.save (2 * tag + 1) next)).pushRegex nfa.size e).size := ih
      _ < _ := by omega
  | alternate e₁ e₂ ih₁ ih₂ =>
    simp [pushRegex]
    calc nfa.size
      _ < (nfa.pushRegex next e₁).size := ih₁
      _ < ((nfa.pushRegex next e₁).pushRegex next e₂).size := ih₂
      _ < _ := by omega
  | concat e₁ e₂ ih₁ ih₂ =>
    simp [pushRegex]
    calc nfa.size
      _ < (nfa.pushRegex next e₂).size := ih₂
      _ < _ := ih₁
  | star greedy e ih =>
    simp [pushRegex, size]
    calc nfa.size
      _ < (nfa.pushNode .fail).size := by simp
      _ < ((nfa.pushNode .fail).pushRegex nfa.size e).size := ih

end Regex.NFA
