-- Equivalance between a Regex match and a NFA path to the .done node
import RegexCorrectness.NFA.Transition.Basic
import RegexCorrectness.NFA.Transition.AcceptOfMatch
import RegexCorrectness.NFA.Transition.MatchOfAccept

namespace NFA

theorem εClosure_of_pathIn {nfa : NFA} {start} (path : nfa.pathIn start i i' []) :
  i' ∈ nfa.εClosure i := by
  generalize h : [] = cs at path
  induction path with
  | base _ => exact .base
  | @step i j k cs cs' step _ ih =>
    simp at h
    simp [h] at *
    cases step with
    | εStep _ _ step =>
      exact εClosure.step (εStep_of_εStep step) ih

theorem pathIn_iff_εClosure {nfa : NFA} :
  nfa.pathIn 0 i i' [] ↔ i' ∈ nfa.εClosure i := by
  apply Iff.intro
  . exact εClosure_of_pathIn
  . intro h
    induction h with
    | base => exact .base (Nat.zero_le _)
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [εStep, lt] at step
        exact .step (.εStep (Nat.zero_le _) lt step) ih
      | isFalse nlt => simp [εStep, nlt] at step

theorem pathToNext_of_compile_of_pathIn' (eq : NFA.compile r = nfa)
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

theorem pathToNext_of_compile_of_pathIn (eq : NFA.compile r = nfa)
  (path : nfa.pathIn 0 nfa.start.val 0 cs) :
  nfa.pathToNext 0 1 nfa.start.val cs := by
  have : 0 < nfa.start.val := by
    rw [←eq, compile]
    exact ge_pushRegex_start (rfl : NFA.done.pushRegex _ r = _)
  exact pathToNext_of_compile_of_pathIn' eq this rfl path

theorem matches_iff_pathToNext {cs : List Char} (eq : NFA.compile r = nfa) :
  r.matches cs ↔ nfa.pathToNext 0 1 nfa.start.val cs :=
  ⟨pathToNext_of_compile_matches eq, matches_of_pathToNext_compile eq⟩

end NFA
