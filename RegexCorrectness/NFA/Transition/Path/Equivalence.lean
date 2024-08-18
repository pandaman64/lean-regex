-- Equivalance between a Regex match and a NFA path to the .done node
import RegexCorrectness.NFA.Transition.Path.Equivalence.PathOfMatch
import RegexCorrectness.NFA.Transition.Path.Equivalence.MatchOfPath

namespace Regex.NFA

theorem pathIn_of_compile_pathInAux {cs : List Char} (eq : compile r = nfa)
  (assm₁ : 0 < i) (assm₂ : next = 0)
  (path : nfa.pathIn 0 i next cs) :
  nfa.pathIn 1 i next cs := by
  have : 0 < nfa.nodes.size := zero_lt_size
  have get : nfa[0] = .done := by
    unfold NFA.compile at eq
    set result := NFA.done.pushRegex ⟨0, by decide⟩ r with h
    simp [←eq]
    rw [pushRegex_get_lt h _ (by decide)]
    rfl
  induction path with
  | last step => exact .last (step.castBound' assm₁)
  | @more i j k cs₁ cs₂ step rest ih =>
    have : 0 < j := by
      apply Nat.zero_lt_of_ne_zero
      intro h
      subst h
      cases rest with
      | last step =>
        have step := step.step
        simp [get, Node.charStep, Node.εStep] at step
      | more step =>
        have step := step.step
        simp [get, Node.charStep, Node.εStep] at step
    exact .more (step.castBound' assm₁) (ih this assm₂)

theorem pathIn_of_compile_pathIn {cs : List Char} (eq : compile r = nfa)
  (path : nfa.pathIn 0 nfa.start.val 0 cs) :
  nfa.pathIn 1 nfa.start.val 0 cs := by
  have : 0 < nfa.start.val := by
    unfold NFA.compile at eq
    set result := NFA.done.pushRegex ⟨0, by decide⟩ r with h
    rw [←eq]
    exact ge_pushRegex_start h
  exact pathIn_of_compile_pathInAux eq this rfl path

theorem matches_iff_pathIn {cs : List Char} (eq : compile r = nfa) :
  r.matches cs ↔ nfa.pathIn 0 nfa.start.val 0 cs := by
  apply Iff.intro
  . intro m
    exact (pathIn_of_compile_matches eq m).castBound (by decide)
  . intro path
    exact matches_of_pathIn_compile eq (pathIn_of_compile_pathIn eq path)

end Regex.NFA
