-- Equivalance between a Regex match and a NFA path to the .done node
import RegexCorrectness.NFA.Transition.Path.Equivalence.PathOfMatch
import RegexCorrectness.NFA.Transition.Path.Equivalence.MatchOfPath

namespace Regex.NFA

theorem pathToNext_of_compile_of_pathInAux (eq : NFA.compile r = nfa)
  (assm₁ : 0 < i) (assm₂ : next = 0)
  (path : nfa.pathIn 0 i next cs) :
  nfa.pathToNext 0 1 i cs := by
  induction path with
  | base _ =>
    subst assm₂
    contradiction
  | @step i j k cs cs' step rest ih =>
    cases rest with
    | base _ =>
      subst assm₂
      exact ⟨i, [], cs, by simp, .base assm₁, step.castStart' assm₁⟩
    | step step' rest =>
      have : 0 < j := by
        cases Nat.eq_or_lt_of_le (Nat.zero_le j) with
        | inl eqj =>
          have : 0 < nfa.nodes.size :=
            calc
              0 < 1 := by decide
              _ < _ := (NFA.done.pushRegex ⟨0, by decide⟩ r).property
              _ = _ := by simp [←eq, compile]
          have hn : nfa[0] = .done := by
            simp [←eq]
            unfold compile
            rw [pushRegex_get_lt rfl 0 (by decide)]
            rfl
          simp [eqj] at hn
          cases step'.step <;> simp [hn, NFA.Node.charStep, NFA.Node.εStep] at *
        | inr gt => exact gt
      have ih := ih this assm₂
      apply ih.cons (step.castStart' assm₁)

theorem pathToNext_of_compile_of_pathIn (eq : compile r = nfa)
  (path : nfa.pathIn 0 nfa.start.val 0 cs) :
  nfa.pathToNext 0 1 nfa.start.val cs := by
  have : 0 < nfa.start.val := by
    rw [←eq, compile]
    exact ge_pushRegex_start (rfl : NFA.done.pushRegex _ r = _)
  exact pathToNext_of_compile_of_pathInAux eq this rfl path

theorem matches_iff_pathToNext {cs : List Char} (eq : compile r = nfa) :
  r.matches cs ↔ nfa.pathToNext 0 1 nfa.start.val cs :=
  ⟨pathToNext_of_compile_matches eq, matches_of_pathToNext_compile eq⟩

end Regex.NFA
