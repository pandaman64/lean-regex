-- Equivalance between evalFrom and pathIn/pathToNext
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

theorem stepSet_of_pathIn {nfa : NFA} (path : nfa.pathIn 0 i i' [c]) :
  i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c := by
  generalize h : [c] = cs at path
  induction path with
  | base _ => contradiction
  | @step i j k cs cs' step path ih =>
    cases step with
    | charStep _ h₂ step =>
      simp at h
      simp [←h] at *
      simp [stepSet]
      exists i
      simp
      simp [εClosureSet]
      exists j, charStep_of_charStep step
      exact εClosure_of_pathIn path
    | εStep _ h₂ step =>
      simp at h
      have ih := ih h
      apply Set.mem_of_mem_of_subset ih
      apply stepSet_subset le_refl
      exact εClosureSet_of_εStep (εStep_of_εStep step)

theorem pathIn_of_stepSet {nfa : NFA} (h : i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c) :
  nfa.pathIn 0 i i' [c] := by
  simp [stepSet, εClosureSet] at h
  let ⟨j, h₁, k, h₂, h₃⟩ := h
  have ⟨lt, h₂'⟩ : ∃ lt : j < nfa.nodes.size, k ∈ nfa[j].charStep c := by
    cases Nat.decLt j nfa.nodes.size with
    | isTrue lt =>
      simp [charStep, lt] at h₂
      exact ⟨lt, h₂⟩
    | isFalse nlt => simp [charStep, nlt] at h₂
  have path₁ : nfa.pathIn 0 i j [] := pathIn_iff_εClosure.mpr h₁
  have path₂ : nfa.pathIn 0 k i' [] := pathIn_iff_εClosure.mpr h₃
  exact path₁.trans (pathIn.step (.charStep (Nat.zero_le _) lt h₂') path₂)

theorem pathIn_iff_stepSet {nfa : NFA} :
  nfa.pathIn 0 i i' [c] ↔ i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c :=
  ⟨stepSet_of_pathIn, pathIn_of_stepSet⟩

theorem evalFrom_of_pathIn {nfa : NFA} {start} (path : nfa.pathIn start i i' cs) :
  i' ∈ nfa.evalFrom {i} cs := by
  induction path with
  | base _ => simp [evalFrom]
  | @step i j k cs cs' step _ ih =>
    simp [evalFrom] at *
    apply Set.mem_of_mem_of_subset ih
    apply foldl_stepSet_subset
    cases step with
    | charStep _ h₂ step =>
      simp [εClosureSet, stepSet]
      simp [Set.subset_def]
      intro k h
      exact ⟨i, .base, j, charStep_of_charStep step, h⟩
    | εStep _ h₂ step =>
      have : {j} ⊆ nfa.εClosureSet {i} := by
        simp
        exact εClosureSet_singleton_step _ step
      have : nfa.εClosureSet {j} ⊆ nfa.εClosureSet (nfa.εClosureSet {i}) :=
        εClosureSet_subset le_refl this
      simp at this
      exact this

theorem pathIn_of_foldl_stepSet {nfa : NFA} (ev : i' ∈ List.foldl nfa.stepSet {i} cs) :
  nfa.pathIn 0 i i' cs := by
  induction cs generalizing i i' with
  | nil =>
    simp at ev
    subst ev
    exact .base (Nat.zero_le _)
  | cons c cs ih =>
    simp at ev
    have : List.foldl nfa.stepSet (nfa.stepSet {i} c) cs =
      ⋃ j ∈ nfa.stepSet {i} c, List.foldl nfa.stepSet {j} cs := by
      have : nfa.stepSet {i} c = ⋃ j ∈ nfa.stepSet {i} c, {j} := by
        simp
      conv =>
        lhs
        rw [this]
      rw [foldl_stepSet_iUnion_distrib]
    simp [this] at ev
    let ⟨j, step, rest⟩ := ev
    have path := ih rest
    show nfa.pathIn 0 i i' ([c] ++ cs)
    apply pathIn.trans _ path
    apply pathIn_iff_stepSet.mpr
    apply Set.mem_of_mem_of_subset step
    apply stepSet_subset le_refl
    simp

theorem pathIn_of_evalFrom {nfa : NFA} (ev : i' ∈ nfa.evalFrom {i} cs) :
  nfa.pathIn 0 i i' cs := by
  unfold evalFrom at ev
  have : nfa.εClosureSet {i} = ⋃ j ∈ nfa.εClosureSet {i}, {j} := by
    simp
  rw [this] at ev
  rw [foldl_stepSet_iUnion_distrib] at ev
  simp at ev
  let ⟨j, step, rest⟩ := ev
  simp [εClosureSet] at step
  have path₁ : nfa.pathIn 0 i j [] := pathIn_iff_εClosure.mpr step
  have path₂ := pathIn_of_foldl_stepSet rest
  exact path₁.trans path₂

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

theorem matches_iff_pathToNext {s : String} (eq : NFA.compile r = nfa) :
  r.matches s ↔ nfa.pathToNext 0 1 nfa.start.val s.data :=
  ⟨pathToNext_of_compile_matches eq, matches_of_pathToNext_compile eq⟩

end NFA
