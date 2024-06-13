import RegexCorrectness.NFA.Basic

namespace Regex.NFA

inductive stepIn (nfa : NFA) (start : Nat) : (current next : Nat) → (cs : List Char) → Prop where
  | charStep {i j : Nat} {c : Char} (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c) : nfa.stepIn start i j [c]
  | εStep {i j : Nat} (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].εStep) : nfa.stepIn start i j []

theorem stepIn.h₁ {nfa : NFA} {start : Nat} {i j : Nat} {cs : List Char}
  (step : nfa.stepIn start i j cs) : start ≤ i := by
  cases step with
  | charStep h₁ _ _ => exact h₁
  | εStep h₁ _ _ => exact h₁

theorem stepIn.h₂ {nfa : NFA} {start : Nat} {i j : Nat} {cs : List Char}
  (step : nfa.stepIn start i j cs) : i < nfa.nodes.size := by
  cases step with
  | charStep _ h₂ _ => exact h₂
  | εStep _ h₂ _ => exact h₂

theorem stepIn.step {nfa : NFA} {start : Nat} {i j : Nat} {cs : List Char}
  (step : nfa.stepIn start i j cs) :
  (∃ c, j ∈ (nfa[i]'step.h₂).charStep c) ∨ j ∈ (nfa[i]'step.h₂).εStep := by
  cases step with
  | charStep _ _ step => exact .inl ⟨_, step⟩
  | εStep _ _ step => exact .inr step

theorem le_of_stepIn {start} (step : stepIn nfa start i j cs) : start ≤ i := by
  cases step with
  | charStep h₁ => exact h₁
  | εStep h₁ => exact h₁

theorem stepIn.lt_right {start} (step : stepIn nfa start i j cs) : j < nfa.nodes.size := by
  match step.step with
  | .inl ⟨_, step⟩ => exact lt_of_charStep step
  | .inr step => exact lt_of_εStep step

theorem stepIn.castStart' {nfa : NFA} {start start' : Nat}
  (le : start' ≤ i) (step : stepIn nfa start i j cs) :
  nfa.stepIn start' i j cs := by
  cases step with
  | charStep h₁ h₂ step => exact .charStep le h₂ step
  | εStep h₁ h₂ step => exact .εStep le h₂ step

theorem stepIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start) (step : stepIn nfa start i j cs) :
  nfa.stepIn start' i j cs := step.castStart' (Nat.le_trans le step.h₁)

theorem stepIn.cast {nfa nfa' : NFA} {start : Nat}
  (step : nfa.stepIn start i j cs)
  (h : i < nfa'.nodes.size)
  (eq : nfa[i]'(step.h₂) = nfa'[i]) :
  nfa'.stepIn start i j cs := by
  cases step with
  | charStep h₁ h₂ step =>
    exact .charStep h₁ h (eq ▸ step)
  | εStep h₁ h₂ step =>
    exact .εStep h₁ h (eq ▸ step)

theorem stepIn.nil_or_singleton {start} (h : stepIn nfa start i j cs) :
  cs = [] ∨ ∃ c, cs = [c] := by
  cases h with
  | εStep => exact .inl rfl
  | charStep => exact .inr ⟨_, rfl⟩

theorem stepIn.nil_of_snoc {start} (h : stepIn nfa start i j (cs ++ [c])) :
  cs = [] := by
  generalize h' : cs ++ [c] = cs' at h
  cases h with
  | εStep => simp at h'
  | charStep =>
    cases cs with
    | nil => rfl
    | cons _ _ =>
      have := congrArg List.length h'
      simp at this

-- Maybe we should recurse from the last as we reason about the last step often
inductive pathIn (nfa : NFA) (start : Nat) : (first : Nat) → (last : Nat) → (cs : List Char) → Prop where
  | base (h : start ≤ i) : nfa.pathIn start i i []
  | step {i j k : Nat} {cs₁ cs₂ : List Char}
    (step : nfa.stepIn start i j cs₁) (rest : nfa.pathIn start j k cs₂) : nfa.pathIn start i k (cs₁ ++ cs₂)

theorem le_of_pathIn_left {start} (path : pathIn nfa start i j cs) : start ≤ i := by
  cases path with
  | base h => exact h
  | step step _ => exact le_of_stepIn step

theorem le_of_pathIn_right {start} (path : pathIn nfa start i j cs) : start ≤ j := by
  induction path with
  | base h => exact h
  | step _ _ ih => exact ih

theorem pathIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start)
  (path : nfa.pathIn start i j cs) :
  nfa.pathIn start' i j cs := by
  induction path with
  | base h => exact .base (Nat.le_trans le h)
  | step step _ ih => exact .step (step.castStart le) ih

theorem pathIn.cast {nfa nfa' : NFA} (start : Nat)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : pathIn nfa start i j cs) :
  pathIn nfa' start i j cs := by
  induction path with
  | base h => exact .base h
  | step step _ ih =>
    let ⟨h, eq⟩ := eq _ step.h₁ step.h₂
    exact .step (step.cast h eq) ih

theorem pathIn.cast' {nfa nfa' : NFA} {start : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (path : pathIn nfa' start i j cs) :
  pathIn nfa start i j cs := by
  induction path with
  | base h => exact .base h
  | @step i j k cs cs' step _ ih =>
    have eq := eq _ step.h₁ assm
    have : j < nfa.nodes.size := by
      cases step with
      | @charStep c _ _ step => exact lt_of_charStep (eq.symm ▸ step)
      | εStep _ _ step => exact lt_of_εStep (eq.symm ▸ step)
    exact .step (step.cast assm eq.symm) (ih this)

theorem pathIn.castLE {nfa : NFA} {start start' i i' : Nat}
  (assm : start' ≤ i)
  (inBounds : ∀ i j, (h₁ : start' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    start ≤ j →
    start' ≤ j)
  (path : pathIn nfa start i i' cs) :
  pathIn nfa start' i i' cs := by
  induction path with
  | base _ => exact .base assm
  | @step i j k cs cs' step rest ih =>
    have h₂ := step.h₂
    have : start' ≤ j := by
      cases step with
      | charStep _ _ step => exact inBounds i j assm h₂ (.inl ⟨_, step⟩) (le_of_pathIn_left rest)
      | εStep _ _ step => exact inBounds i j assm h₂ (.inr step) (le_of_pathIn_left rest)
    exact .step (step.castStart' assm) (ih this)

theorem pathIn.lt_right {nfa : NFA} {start i i' : Nat}
  (assm : i < nfa.nodes.size)
  (path : pathIn nfa start i i' cs) :
  i' < nfa.nodes.size := by
  induction path with
  | base _ => exact assm
  | @step i j _ _ _ step _ ih =>
    have : j < nfa.nodes.size := by
      cases step with
      | charStep _ _ step => exact lt_of_charStep step
      | εStep _ _ step => exact lt_of_εStep step
    exact ih this

theorem pathIn.snoc_char {start}
  (assm : j < nfa.nodes.size)
  (step : k ∈ nfa[j].charStep c) (path : pathIn nfa start i j cs)
  : pathIn nfa (min start k) i k (cs ++ [c]) := by
  induction path with
  | base h =>
    simp
    exact .step (.charStep (Nat.le_trans (Nat.min_le_left _ _) h) assm step) (.base (Nat.min_le_right _ _))
  | @step i j k' cs'' cs''' step' rest ih =>
    simp
    have ih := ih assm step
    exact pathIn.step (step'.castStart (Nat.min_le_left _ _)) ih

theorem pathIn.snoc_ε {start}
  (assm : j < nfa.nodes.size)
  (step : k ∈ nfa[j].εStep) (path : pathIn nfa start i j cs)
  : pathIn nfa (min start k) i k cs := by
  induction path with
  | base h =>
    exact .step (.εStep (Nat.le_trans (Nat.min_le_left _ _) h) assm step) (.base (Nat.min_le_right _ _))
  | step step' rest ih =>
    have ih := ih assm step
    exact .step (step'.castStart (Nat.min_le_left _ _)) ih

theorem pathIn.trans {start}
  (path₁ : pathIn nfa start i j cs) (path₂ : pathIn nfa start j k cs') :
  pathIn nfa start i k (cs ++ cs') := by
  induction path₁ with
  | base _ => exact path₂
  | step step _ ih =>
    simp
    exact .step step (ih path₂)

def pathToNext (nfa : NFA) (next start i : Nat) (cs : List Char) : Prop :=
  ∃ (i' : Nat) (pcs scs : List Char),
    cs = pcs ++ scs ∧
    nfa.pathIn start i i' pcs ∧
    nfa.stepIn start i' next scs

theorem le_of_pathToNext {start} (path : pathToNext nfa next start i cs) : start ≤ i := by
  obtain ⟨_, _, _, _, path, _⟩ := path
  exact le_of_pathIn_left path

theorem pathToNext.cons {start} {cs₁ cs₂ : List Char}
  (step : stepIn nfa start i j cs₁) (path : pathToNext nfa next start j cs₂) :
  pathToNext nfa next start i (cs₁ ++ cs₂) := by
  obtain ⟨i', pcs, scs, eqs, path, step'⟩ := path
  subst eqs
  cases step with
  | charStep h₁ h₂ step =>
    exact ⟨i', _ :: pcs, scs, rfl, .step (.charStep h₁ h₂ step) path, step'⟩
  | εStep h₁ h₂ step =>
    exact ⟨i', pcs, scs, rfl, .step (.εStep h₁ h₂ step) path, step'⟩

theorem pathToNext.cast {nfa nfa' : NFA} {next start i : Nat} {cs : List Char}
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : pathToNext nfa next start i cs) :
  pathToNext nfa' next start i cs := by
  obtain ⟨i', pcs, scs, eqs, path, step⟩ := path
  obtain ⟨h', eq'⟩ := eq _ (le_of_pathIn_right path) step.h₂
  exact ⟨i', pcs, scs, eqs, pathIn.cast start eq path, step.cast h' eq'⟩

theorem pathToNext.cast' {nfa nfa' : NFA} {start : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (path : pathToNext nfa' next start i cs) :
  pathToNext nfa next start i cs := by
  obtain ⟨i', pcs, scs, eqs, path, step⟩ := path
  have path' := path.cast' assm le eq
  have lt : i' < nfa.nodes.size := path'.lt_right assm
  exact ⟨i', pcs, scs, eqs, path', step.cast lt (eq i' step.h₁ lt).symm⟩

theorem pathToNext.castStart {nfa : NFA} {start start' : Nat} {i : Nat} {cs : List Char}
  (le : start' ≤ start) (path : pathToNext nfa next start i cs) :
  pathToNext nfa next start' i cs := by
  obtain ⟨i', pcs, scs, eqs, path, step⟩ := path
  exact ⟨i', pcs, scs, eqs, path.castStart le, step.castStart le⟩

theorem pathToNext.castLE {nfa : NFA} {next start start' i : Nat} {cs : List Char}
  (assm : start' ≤ i)
  (inBounds : ∀ i j, (h₁ : start' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    start ≤ j →
    start' ≤ j)
  (path : pathToNext nfa next start i cs) :
  pathToNext nfa next start' i cs := by
  obtain ⟨i', pcs, scs, eqs, path, step⟩ := path
  have path' := path.castLE assm inBounds
  exact ⟨i', pcs, scs, eqs, path', step.castStart' (le_of_pathIn_right path')⟩

theorem pathToNext.trans {nfa : NFA} {start : Nat} {cs cs' : List Char}
  (path₁ : pathToNext nfa j start i cs) (path₂ : pathToNext nfa k start j cs') :
  pathToNext nfa k start i (cs ++ cs') := by
  obtain ⟨i₁, pcs₁, scs₁, eqs₁, path₁, step₁⟩ := path₁
  obtain ⟨i₂, pcs₂, scs₂, eqs₂, path₂, step₂⟩ := path₂
  exact ⟨i₂, pcs₁ ++ (scs₁ ++ pcs₂), scs₂, by simp [eqs₁, eqs₂], path₁.trans (.step step₁ path₂), step₂⟩

theorem pathIn_of_pathToNext {nfa : NFA} {start : Nat}
  (path : pathToNext nfa next start i cs) :
  pathIn nfa (min start next) i next cs := by
  obtain ⟨i', pcs, scs, eqs, path, step⟩ := path
  cases step with
  | charStep h₁ h₂ step => exact eqs ▸ path.snoc_char h₂ step
  | εStep h₁ h₂ step => simp [eqs, path.snoc_ε h₂ step]

end Regex.NFA
