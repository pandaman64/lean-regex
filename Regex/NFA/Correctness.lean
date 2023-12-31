import Regex.NFA.Transition

namespace NFA

theorem evalFrom_of_pathIn {nfa : NFA} (path : nfa.pathIn start i cs i' []) :
  i' ∈ nfa.evalFrom {i} cs := by
  generalize h : [] = cs'
  rw [h] at path
  induction path with
  | base _ eqi eqs =>
    subst h eqi eqs
    simp [NFA.evalFrom]
  | @charStep i j k c _ _ _ h₂ step _ ih =>
    have ih := ih h
    simp [NFA.evalFrom] at *
    have : nfa.εClosureSet {j} ⊆ nfa.stepSet (nfa.εClosureSet {i}) c := by
      simp [NFA.εClosureSet, NFA.stepSet]
      simp [Set.subset_def]
      intro k h
      refine ⟨i, ?_, j, ?_, h⟩
      . exact .base
      . simp [getElem?_pos nfa i h₂, Option.charStep, step]
    exact Set.mem_of_mem_of_subset ih (foldl_stepSet_subset this)
  | @εStep i j k _ _ _ h₂ step _ ih =>
    have ih := ih h
    simp [NFA.evalFrom] at *
    have : nfa.εClosureSet {j} ⊆ nfa.εClosureSet {i} := by
      have : {j} ⊆ nfa.εClosureSet {i} := by
        simp
        have : j ∈ nfa[i]?.εStep := by
          simp [getElem?_pos nfa i h₂]
          simp [Option.εStep, step]
        exact εClosureSet_singleton_step this
      have : nfa.εClosureSet {j} ⊆ nfa.εClosureSet (nfa.εClosureSet {i}) :=
        εClosureSet_subset (le_refl _) this
      simp at this
      exact this
    exact Set.mem_of_mem_of_subset ih (foldl_stepSet_subset this)

theorem NFA.pathToNext.asPathInFromZero {nfa : NFA} {start}
  (path : nfa.pathToNext next start i cs []) :
  nfa.pathIn 0 i cs next [] := by
  cases path with
  | charStep i' h c step path => exact (path.snoc_char h rfl step).castStart (Nat.zero_le _)
  | εStep i' h step path => exact (path.snoc_ε h step).castStart (Nat.zero_le _)

theorem pathIn_of_evalFrom {nfa : NFA} (ev : i' ∈ nfa.evalFrom {i} cs) :
  nfa.pathIn 0 i cs i' [] := by
  induction cs generalizing i i' with
  | nil => sorry -- in εClosure
  | cons c cs ih =>
    simp [NFA.evalFrom] at ev
    sorry

-- TODO: establish that for `nfa = compile r`, `nfa.pathIn 0 i cs i' []` implies
-- `nfa.pathToNext 0 1 i cs []`. Essentially, we don't step to 0 except at the end.
-- Then, we can prove that evalFrom implies pathToNext, closing the loop.

end NFA
