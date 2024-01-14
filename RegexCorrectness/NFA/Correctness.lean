import RegexCorrectness.NFA.Transition

namespace NFA

theorem εClosureSet_of_εStep {nfa : NFA} {i j : Nat} (h : i < nfa.nodes.size)
  (step : j ∈ nfa[i].εStep) :
  nfa.εClosureSet {j} ⊆ nfa.εClosureSet {i} := by
  have : j ∈ nfa[i]?.εStep := by
    simp [Option.εStep, getElem?_pos nfa i h, step]
  have : {j} ⊆ nfa.εClosureSet {i} := by
    simp [NFA.εClosureSet]
    exact NFA.εClosure.step this .base
  have : nfa.εClosureSet {j} ⊆ nfa.εClosureSet (nfa.εClosureSet {i}) :=
    εClosureSet_subset (le_refl _) this
  simp at this
  exact this

theorem ge_length_of_pathIn {nfa : NFA} (path : nfa.pathIn start i cs i' cs') :
  cs.length ≥ cs'.length := by
  induction path with
  | base _ _ eqs => rw [eqs]
  | step step _ ih =>
    cases step with
    | charStep =>
      simp
      exact Nat.le_trans ih (Nat.le_succ _)
    | εStep => exact ih

theorem εClosure_of_pathIn {nfa : NFA} (eq : cs = cs') (path : nfa.pathIn 0 i cs i' cs') :
  i' ∈ nfa.εClosure i := by
  induction path with
  | base _ eqi => rw [eqi]; exact .base
  | @step i j k cs cs' cs'' step rest ih =>
    cases step with
    | charStep _ _ step =>
      have ge_length := ge_length_of_pathIn rest
      subst eq
      simp at ge_length
      have not_lt := Nat.not_lt_of_ge ge_length
      exact absurd (Nat.lt_succ_self _) not_lt
    | εStep _ h₂ step =>
      have : j ∈ nfa[i]?.εStep := by
        simp [Option.εStep, getElem?_pos nfa i h₂, step]
      exact NFA.εClosure.step this (ih eq)

theorem pathIn_iff_εClosure {nfa : NFA} :
  nfa.pathIn 0 i cs i' cs ↔ i' ∈ nfa.εClosure i := by
  apply Iff.intro
  . exact εClosure_of_pathIn rfl
  . intro h
    induction h with
    | base => exact .base (Nat.zero_le _) rfl rfl
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [Option.εStep, getElem?_pos nfa i lt] at step
        exact .step (.εStep (Nat.zero_le _) lt step) ih
      | isFalse nlt => simp [Option.εStep, getElem?_neg nfa i nlt] at step

theorem stepSet_of_pathIn {nfa : NFA} (eq₁ : cs₁ = c :: cs) (eq₂ : cs₂ = cs)
  (path : nfa.pathIn 0 i cs₁ i' cs₂) :
  i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c := by
  induction path with
  | base _ _ eqs =>
    subst eqs eq₁
    exact absurd eq₂ (List.cons_ne_self _ _)
  | @step i j k cs cs' cs'' step path ih =>
    cases step with
    | charStep _ h₂ step =>
      apply List.noConfusion eq₁
      intro eq₃ eq₄
      subst eq₂ eq₃ eq₄
      simp [NFA.stepSet]
      exists i
      simp [Option.charStep, getElem?_pos nfa i h₂]
      simp [NFA.εClosureSet]
      exists j, step
      exact εClosure_of_pathIn rfl path
    | εStep _ h₂ step =>
      have ih := ih eq₁ eq₂
      apply Set.mem_of_mem_of_subset ih
      apply stepSet_subset (le_refl _)
      exact εClosureSet_of_εStep h₂ step

theorem pathIn_of_stepSet {nfa : NFA} (h : i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c) :
  nfa.pathIn 0 i (c :: cs) i' cs := by
  simp [NFA.stepSet, NFA.εClosureSet] at h
  let ⟨j, h₁, k, h₂, h₃⟩ := h
  have h₂' : ∃ lt : j < nfa.nodes.size, k ∈ nfa[j].charStep c := by
    cases Nat.decLt j nfa.nodes.size with
    | isTrue lt =>
      simp [Option.charStep, getElem?_pos nfa j lt] at h₂
      exact ⟨lt, h₂⟩
    | isFalse nlt => simp [Option.charStep, getElem?_neg nfa j nlt] at h₂
  let ⟨lt, h₂'⟩ := h₂'
  have path₁ : nfa.pathIn 0 i (c :: cs) j (c :: cs) := pathIn_iff_εClosure.mpr h₁
  have path₂ : nfa.pathIn 0 k cs i' cs := pathIn_iff_εClosure.mpr h₃
  exact path₁.trans (NFA.pathIn.step (.charStep (Nat.zero_le _) lt h₂') path₂)

theorem pathIn_iff_stepSet {nfa : NFA} :
  nfa.pathIn 0 i (c :: cs) i' cs ↔ i' ∈ nfa.stepSet (nfa.εClosureSet {i}) c := by
  apply Iff.intro
  . exact stepSet_of_pathIn rfl rfl
  . exact pathIn_of_stepSet

theorem evalFrom_of_pathIn {nfa : NFA} (path : nfa.pathIn start i cs i' []) :
  i' ∈ nfa.evalFrom {i} cs := by
  generalize h : [] = cs'
  rw [h] at path
  induction path with
  | base _ eqi eqs =>
    subst h eqi eqs
    simp [NFA.evalFrom]
  | @step i j k cs cs' cs'' step _ ih =>
    have ih := ih h
    simp [NFA.evalFrom] at *
    apply Set.mem_of_mem_of_subset ih
    cases step with
    | charStep _ h₂ step =>
      simp
      apply foldl_stepSet_subset
      simp [NFA.εClosureSet, NFA.stepSet]
      simp [Set.subset_def]
      intro k h
      refine ⟨i, ?_, j, ?_, h⟩
      . exact .base
      . simp [getElem?_pos nfa i h₂, Option.charStep, step]
    | εStep _ h₂ step =>
      apply foldl_stepSet_subset
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

theorem stepSet_iUnion_distrib {nfa : NFA} {f : α → Set Nat} {S : Set α} {c : Char} :
  nfa.stepSet (⋃ i ∈ S, f i) c = ⋃ i ∈ S, nfa.stepSet (f i) c := by
  simp [NFA.stepSet]

theorem foldl_stepSet_iUnion_distrib {nfa : NFA} {f : α → Set Nat} {S : Set α} {cs : List Char} :
  List.foldl nfa.stepSet (⋃ i ∈ S, f i) cs = ⋃ i ∈ S, List.foldl nfa.stepSet (f i) cs := by
  induction cs generalizing f with
  | nil => simp
  | cons c cs ih =>
    simp [stepSet_iUnion_distrib]
    exact ih

theorem pathIn_of_foldl_stepSet {nfa : NFA} (ev : i' ∈ List.foldl nfa.stepSet {i} cs) :
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
    apply NFA.pathIn.trans _ path
    apply pathIn_iff_stepSet.mpr
    apply Set.mem_of_mem_of_subset step
    apply stepSet_subset (le_refl _)
    simp

theorem pathIn_of_evalFrom {nfa : NFA} (ev : i' ∈ nfa.evalFrom {i} cs) :
  nfa.pathIn 0 i cs i' [] := by
  unfold NFA.evalFrom at ev
  have : nfa.εClosureSet {i} = ⋃ j ∈ nfa.εClosureSet {i}, {j} := by
    simp
  rw [this] at ev
  rw [foldl_stepSet_iUnion_distrib] at ev
  simp at ev
  let ⟨j, step, rest⟩ := ev
  simp [NFA.εClosureSet] at step
  have path₁ : nfa.pathIn 0 i cs j cs := pathIn_iff_εClosure.mpr step
  have path₂ := pathIn_of_foldl_stepSet rest
  exact path₁.trans path₂

theorem pathToNext_of_compile_of_pathIn (eq : compile.loop r 0 compile.init = result)
  (assm₁ : 0 < i) (assm₂ : next = 0) (assm₃ : cs' = []) (assm₄ : nfa = result.val)
  (path : nfa.pathIn 0 i cs next cs') :
  nfa.pathToNext 0 1 i cs [] := by
  induction path with
  | base _ eqi =>
    subst eqi assm₂
    contradiction
  | @step i j k cs cs' cs'' step rest ih =>
    cases rest with
    | base _ eqi eqs =>
      subst eqi eqs assm₂ assm₃
      exact ⟨i, cs, .base assm₁ rfl rfl, step.castStart' assm₁⟩
    | step step' rest =>
      have : 0 < j := by
        cases step' with
        | charStep _ h₂ step' => exact gt_zero_char eq (assm₄ ▸ h₂) (by simp [assm₄] at step'; exact step')
        | εStep _ h₂ step' => exact gt_zero_ε eq (assm₄ ▸ h₂) (by simp [assm₄] at step'; exact step')
      have ih := ih this assm₂ assm₃
      exact ih.cons (step.castStart' assm₁)
where
  gt_zero_char {j j'} {c} (eq : compile.loop r 0 compile.init = result)
    (h : j < result.val.nodes.size) (step : j' ∈ result.val[j].charStep c) : 0 < j := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le j) with
    | inl eqj =>
      subst eqj
      simp [compile.loop.get_lt (i := 0) eq (by decide)] at step
      simp [Node.charStep, compile.init.get] at step
    | inr gt => exact gt
  gt_zero_ε {j j'} (eq : compile.loop r 0 compile.init = result)
    (h : j < result.val.nodes.size) (step : j' ∈ result.val[j].εStep) : 0 < j := by
    cases Nat.eq_or_lt_of_le (Nat.zero_le j) with
    | inl eqj =>
      subst eqj
      simp [compile.loop.get_lt (i := 0) eq (by decide)] at step
      simp [Node.εStep, compile.init.get] at step
    | inr gt => exact gt

theorem pathToNext_of_compile_of_pathIn' (eq : compile r = nfa) (path : nfa.pathIn 0 nfa.start cs 0 []) :
  nfa.pathToNext 0 1 nfa.start cs [] := by
  generalize eq' : compile.loop r 0 compile.init = result
  have eq'' : nfa = result.val := by
    simp [eq.symm, compile, eq'.symm]
  have : 0 < nfa.start.val := compile.start_gt eq
  exact pathToNext_of_compile_of_pathIn eq' this rfl rfl eq'' path

-- Correctness of the NFA compilation

theorem evalFrom_of_matches' (eq : compile r = nfa) (m : r.matches ⟨cs⟩) :
  0 ∈ nfa.evalFrom {nfa.start.val} cs := by
  generalize eq' : compile.loop r 0 compile.init = result
  have : nfa = result.val := by
    simp [eq.symm, compile, eq'.symm]
  rw [this]
  exact evalFrom_of_matches eq' m result.val (le_refl _)

theorem matches_of_evalFrom' (eq : compile r = nfa) (ev : 0 ∈ nfa.evalFrom {nfa.start.val} cs) :
  r.matches ⟨cs⟩ := by
  generalize eq' : compile.loop r 0 compile.init = result
  have : nfa = result.val := by
    simp [eq.symm, compile, eq'.symm]
  rw [this] at ev
  have path := pathIn_of_evalFrom ev
  subst this
  have path : NFA.pathToNext result 0 1 result.val.start cs [] :=
    pathToNext_of_compile_of_pathIn' eq path
  exact matches_of_path eq path

end NFA
