-- Equivalance between evalFrom and pathIn/pathToNext
import RegexCorrectness.NFA.Transition.Basic
import RegexCorrectness.NFA.Transition.AcceptOfMatch

namespace NFAa

theorem ge_length_of_pathIn {start} {nfa : NFAa} (path : nfa.pathIn start i cs i' cs') :
  cs.length ≥ cs'.length := by
  induction path with
  | base _ _ eqs => rw [eqs]
  | step step _ ih =>
    cases step with
    | charStep =>
      simp
      exact Nat.le_trans ih (Nat.le_succ _)
    | εStep => exact ih

theorem εClosure_of_pathIn {nfa : NFAa} (eq : cs = cs') (path : nfa.pathIn 0 i cs i' cs') :
  i' ∈ nfa.εClosure i := by
  induction path with
  | base _ eqi => rw [eqi]; exact .base
  | @step i j k cs cs' cs'' step rest ih =>
    cases step with
    | charStep _ _ step =>
      have ge_length := ge_length_of_pathIn rest
      subst eq
      simp at ge_length
      exact absurd ge_length (Nat.lt_irrefl _)
    | εStep _ h₂ step =>
      exact εClosure.step (εStep_of_εStep step) (ih eq)

theorem pathIn_iff_εClosure {nfa : NFAa} :
  nfa.pathIn 0 i cs i' cs ↔ i' ∈ nfa.εClosure i := by
  apply Iff.intro
  . exact εClosure_of_pathIn rfl
  . intro h
    induction h with
    | base => exact .base (Nat.zero_le _) rfl rfl
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [εStep, lt] at step
        exact .step (.εStep (Nat.zero_le _) lt step) ih
      | isFalse nlt => simp [εStep, nlt] at step

theorem stepSet_of_pathIn {nfa : NFAa} (eq₁ : cs₁ = c :: cs) (eq₂ : cs₂ = cs)
  (path : nfa.pathIn 0 i cs₁ i' cs₂) :
  i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c := by
  induction path with
  | base _ _ eqs =>
    subst eqs eq₁
    exact absurd eq₂ (List.cons_ne_self _ _)
  | @step i j k cs cs' cs'' step path ih =>
    cases step with
    | charStep _ h₂ step =>
      simp at eq₁
      simp [eq₁] at *
      simp [stepSet]
      exists i
      simp
      simp [εClosureSet]
      exists j, charStep_of_charStep step
      exact εClosure_of_pathIn eq₂.symm path
    | εStep _ h₂ step =>
      have ih := ih eq₁ eq₂
      apply Set.mem_of_mem_of_subset ih
      apply stepSet_subset le_refl
      exact εClosureSet_of_εStep (εStep_of_εStep step)

theorem pathIn_of_stepSet {nfa : NFAa} (h : i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c) :
  nfa.pathIn 0 i (c :: cs) i' cs := by
  simp [stepSet, εClosureSet] at h
  let ⟨j, h₁, k, h₂, h₃⟩ := h
  have ⟨lt, h₂'⟩ : ∃ lt : j < nfa.nodes.size, k ∈ nfa[j].charStep c := by
    cases Nat.decLt j nfa.nodes.size with
    | isTrue lt =>
      simp [charStep, lt] at h₂
      exact ⟨lt, h₂⟩
    | isFalse nlt => simp [charStep, nlt] at h₂
  have path₁ : nfa.pathIn 0 i (c :: cs) j (c :: cs) := pathIn_iff_εClosure.mpr h₁
  have path₂ : nfa.pathIn 0 k cs i' cs := pathIn_iff_εClosure.mpr h₃
  exact path₁.trans (pathIn.step (.charStep (Nat.zero_le _) lt h₂') path₂)

theorem pathIn_iff_stepSet {nfa : NFAa} :
  nfa.pathIn 0 i (c :: cs) i' cs ↔ i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c := by
  apply Iff.intro
  . exact stepSet_of_pathIn rfl rfl
  . exact pathIn_of_stepSet

theorem evalFrom_of_pathIn {nfa : NFAa} {start} (path : nfa.pathIn start i cs i' []) :
  i' ∈ nfa.evalFrom {i} cs := by
  generalize h : [] = cs'
  rw [h] at path
  induction path with
  | base _ eqi eqs =>
    subst h eqi eqs
    simp [evalFrom]
  | @step i j k cs cs' cs'' step _ ih =>
    have ih := ih h
    simp [evalFrom] at *
    apply Set.mem_of_mem_of_subset ih
    cases step with
    | charStep _ h₂ step =>
      simp
      apply foldl_stepSet_subset
      simp [εClosureSet, stepSet]
      simp [Set.subset_def]
      intro k h
      refine ⟨i, .base, j, charStep_of_charStep step, h⟩
    | εStep _ h₂ step =>
      apply foldl_stepSet_subset
      have : {j} ⊆ nfa.εClosureSet {i} := by
        simp
        exact εClosureSet_singleton_step _ step
      have : nfa.εClosureSet {j} ⊆ nfa.εClosureSet (nfa.εClosureSet {i}) :=
        εClosureSet_subset le_refl this
      simp at this
      exact this

theorem pathIn_of_foldl_stepSet {nfa : NFAa} (ev : i' ∈ List.foldl nfa.stepSet {i} cs) :
  nfa.pathIn 0 i cs i' [] := by
  induction cs generalizing i i' with
  | nil =>
    simp at ev
    subst ev
    exact .base (Nat.zero_le _) rfl rfl
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
    apply pathIn.trans _ path
    apply pathIn_iff_stepSet.mpr
    apply Set.mem_of_mem_of_subset step
    apply stepSet_subset le_refl
    simp

theorem pathIn_of_evalFrom {nfa : NFAa} (ev : i' ∈ nfa.evalFrom {i} cs) :
  nfa.pathIn 0 i cs i' [] := by
  unfold evalFrom at ev
  have : nfa.εClosureSet {i} = ⋃ j ∈ nfa.εClosureSet {i}, {j} := by
    simp
  rw [this] at ev
  rw [foldl_stepSet_iUnion_distrib] at ev
  simp at ev
  let ⟨j, step, rest⟩ := ev
  simp [εClosureSet] at step
  have path₁ : nfa.pathIn 0 i cs j cs := pathIn_iff_εClosure.mpr step
  have path₂ := pathIn_of_foldl_stepSet rest
  exact path₁.trans path₂

theorem pathToNext_of_compile_of_pathIn' (eq : NFAa.compile r = nfa)
  (assm₁ : 0 < i) (assm₂ : next = 0)
  (path : nfa.pathIn 0 i cs next cs') :
  nfa.pathToNext 0 1 i cs cs' := by
  induction path with
  | base _ eqi =>
    subst eqi assm₂
    contradiction
  | @step i j k cs cs' cs'' step rest ih =>
    cases rest with
    | base _ eqi eqs =>
      subst eqi eqs assm₂
      exact ⟨i, cs, .base assm₁ rfl rfl, step.castStart' assm₁⟩
    | step step' rest =>
      have : 0 < j := by
        cases Nat.eq_or_lt_of_le (Nat.zero_le j) with
        | inl eqj =>
          have : 0 < nfa.nodes.size :=
            calc
              0 < 1 := by decide
              _ < _ := (NFAa.done.pushRegex ⟨0, by decide⟩ r).property
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

theorem pathToNext_of_compile_of_pathIn (eq : NFAa.compile r = nfa)
  (path : nfa.pathIn 0 nfa.start.val cs 0 []) :
  nfa.pathToNext 0 1 nfa.start.val cs [] := by
  have : 0 < nfa.start.val := by
    rw [←eq, compile]
    exact ge_pushRegex_start (rfl : NFAa.done.pushRegex _ r = _)
  exact pathToNext_of_compile_of_pathIn' eq this rfl path

end NFAa
