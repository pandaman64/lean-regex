import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile

namespace NFA

inductive stepIn (nfa : NFA) (start : Nat) : (current: Nat) → (input: List Char) → (next: Nat) → (output: List Char) → Prop where
  | charStep {i j : Nat} {c : Char} {cs : List Char} (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].charStep c) : nfa.stepIn start i (c :: cs) j cs
  | εStep {i j : Nat} {cs : List Char} (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (step : j ∈ nfa[i].εStep) : nfa.stepIn start i cs j cs

theorem Array.is_empty (x : Array α) (h : x.isEmpty) : x = #[] :=
  match x with
  | ⟨[]⟩      => rfl
  | ⟨_ :: _⟩  => nomatch h

theorem stepIn.empty_sparse {i j start : Nat} (nfa : NFA) (h₁ : start ≤ i) (h₂ : i < nfa.nodes.size) (h₃ : e.isEmpty) (x : nfa[i] = Node.sparse e z) : ¬stepIn nfa start i c j c' := by
  intro h
  match h with
  | charStep _ _ step =>
      rw [x] at step
      let res := Array.is_empty e h₃
      rw [res] at step
      contradiction
  | εStep _ _ step =>
      rw [x] at step
      contradiction

theorem stepIn.h₁ {nfa : NFA} {start : Nat} {i j : Nat} {cs cs' : List Char}
  (step : nfa.stepIn start i cs j cs') : start ≤ i := by
  cases step with
  | charStep h₁ _ _ => exact h₁
  | εStep h₁ _ _ => exact h₁

theorem stepIn.h₂ {nfa : NFA} {start : Nat} {i j : Nat} {cs cs' : List Char}
  (step : nfa.stepIn start i cs j cs') : i < nfa.nodes.size := by
  cases step with
  | charStep _ h₂ _ => exact h₂
  | εStep _ h₂ _ => exact h₂

theorem stepIn.step {nfa : NFA} {start : Nat} {i j : Nat} {cs cs' : List Char}
  (step : nfa.stepIn start i cs j cs') :
  (∃ c, j ∈ (nfa[i]'step.h₂).charStep c) ∨ j ∈ (nfa[i]'step.h₂).εStep := by
  cases step with
  | charStep _ _ step => exact .inl ⟨_, step⟩
  | εStep _ _ step => exact .inr step

theorem le_of_stepIn {start} (step : stepIn nfa start i cs j cs') : start ≤ i := by
  cases step with
  | charStep h₁ => exact h₁
  | εStep h₁ => exact h₁

theorem stepIn.lt_right {start} (step : stepIn nfa start i cs j cs') : j < nfa.nodes.size := by
  match step.step with
  | .inl ⟨_, step⟩ => exact lt_of_charStep step
  | .inr step => exact lt_of_εStep step

theorem stepIn.castStart' {nfa : NFA} {start start' : Nat}
  (le : start' ≤ i) (step : stepIn nfa start i cs j cs') :
  nfa.stepIn start' i cs j cs' := by
  cases step with
  | charStep h₁ h₂ step => exact .charStep le h₂ step
  | εStep h₁ h₂ step => exact .εStep le h₂ step

theorem stepIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start) (step : stepIn nfa start i cs j cs') :
  nfa.stepIn start' i cs j cs' := step.castStart' (Nat.le_trans le step.h₁)

theorem stepIn.cast {nfa nfa' : NFA} {start : Nat}
  (step : nfa.stepIn start i cs j cs')
  (h : i < nfa'.nodes.size)
  (eq : nfa[i]'(step.h₂) = nfa'[i]) :
  nfa'.stepIn start i cs j cs' := by
  cases step with
  | charStep h₁ h₂ step =>
    exact .charStep h₁ h (eq ▸ step)
  | εStep h₁ h₂ step =>
    exact .εStep h₁ h (eq ▸ step)

-- Maybe we should recurse from the last as we reason about the last step often
inductive pathIn (nfa : NFA) (start : Nat) : (index: Nat) → (prefx: List Char) → (next: Nat) → List Char → Prop where
  | base (h : start ≤ i) (eqi : i = j) (eqs : cs = cs') : nfa.pathIn start i cs j cs'
  | step {i j k : Nat} {cs cs' cs'' : List Char} (step : nfa.stepIn start i cs j cs') (rest : nfa.pathIn start j cs' k cs'') : nfa.pathIn start i cs k cs''

theorem le_of_pathIn_left {start} (path : pathIn nfa start i cs j cs') : start ≤ i := by
  cases path with
  | base h => exact h
  | step step _ => exact le_of_stepIn step

theorem le_of_pathIn_right {start} (path : pathIn nfa start i cs j cs') : start ≤ j := by
  induction path with
  | base h eqi => exact eqi ▸ h
  | step _ _ ih => exact ih

theorem pathIn.castStart {nfa : NFA} {start start' : Nat}
  (le : start' ≤ start)
  (path : nfa.pathIn start i cs j cs') :
  nfa.pathIn start' i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base (Nat.le_trans le h) eqi eqs
  | step step _ ih => exact .step (step.castStart le) ih

theorem pathIn.cast {nfa nfa' : NFA} (start : Nat)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : pathIn nfa start i cs j cs') :
  pathIn nfa' start i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base h eqi eqs
  | step step _ ih =>
    let ⟨h, eq⟩ := eq _ step.h₁ step.h₂
    exact .step (step.cast h eq) ih

theorem pathIn.cast' {nfa nfa' : NFA} {start : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (path : pathIn nfa' start i cs j cs') :
  pathIn nfa start i cs j cs' := by
  induction path with
  | base h eqi eqs => exact .base h eqi eqs
  | @step i j k cs cs' cs'' step _ ih =>
    have eq := eq _ step.h₁ assm
    have : j < nfa.nodes.size := by
      cases step with
      | @charStep _ c _ _ _ step => exact lt_of_charStep (eq.symm ▸ step)
      | εStep _ _ step => exact lt_of_εStep (eq.symm ▸ step)
    exact .step (step.cast assm eq.symm) (ih this)

theorem pathIn.castLE {nfa : NFA} {start start' i i' : Nat}
  (assm : start' ≤ i)
  (inBounds : ∀ i j, (h₁ : start' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    start ≤ j →
    start' ≤ j)
  (path : pathIn nfa start i cs i' cs') :
  pathIn nfa start' i cs i' cs' := by
  induction path with
  | base _ eqi eqs => exact .base assm eqi eqs
  | @step i j k cs cs' cs'' step rest ih =>
    have h₂ := step.h₂
    have : start' ≤ j := by
      cases step with
      | charStep _ _ step => exact inBounds i j assm h₂ (.inl ⟨_, step⟩) (le_of_pathIn_left rest)
      | εStep _ _ step => exact inBounds i j assm h₂ (.inr step) (le_of_pathIn_left rest)
    exact .step (step.castStart' assm) (ih this)

theorem pathIn.lt_right {nfa : NFA} {start i i' : Nat}
  (assm : i < nfa.nodes.size)
  (path : pathIn nfa start i cs i' cs') :
  i' < nfa.nodes.size := by
  induction path with
  | base _ eqi _ => exact eqi ▸ assm
  | @step i j _ _ _ _ step _ ih =>
    have : j < nfa.nodes.size := by
      cases step with
      | charStep _ _ step => exact lt_of_charStep step
      | εStep _ _ step => exact lt_of_εStep step
    exact ih this

theorem pathIn.snoc_char {start}
  (assm₁ : j < nfa.nodes.size) (assm₂ : cs' = c :: cs'')
  (step : k ∈ nfa[j].charStep c) (path : pathIn nfa start i cs j cs')
  : pathIn nfa (min start k) i cs k cs'' := by
  induction path with
  | base h eqi eqs =>
    subst eqi eqs assm₂
    exact .step (.charStep (Nat.le_trans (Nat.min_le_left _ _) h) assm₁ step) (.base (Nat.min_le_right _ _) rfl rfl)
  | step step' rest ih =>
    have ih := ih assm₁ assm₂ step
    exact .step (step'.castStart (Nat.min_le_left _ _)) ih

theorem pathIn.snoc_ε {start}
  (assm : j < nfa.nodes.size)
  (step : k ∈ nfa[j].εStep) (path : pathIn nfa start i cs j cs')
  : pathIn nfa (min start k) i cs k cs' := by
  induction path with
  | base h eqi eqs =>
    subst eqi eqs
    exact .step (.εStep (Nat.le_trans (Nat.min_le_left _ _) h) assm step) (.base (Nat.min_le_right _ _) rfl rfl)
  | step step' rest ih =>
    have ih := ih assm step
    exact .step (step'.castStart (Nat.min_le_left _ _)) ih

theorem pathIn.trans {start}
  (path₁ : pathIn nfa start i cs j cs') (path₂ : pathIn nfa start j cs' k cs'') :
  pathIn nfa start i cs k cs'' := by
  induction path₁ with
  | base _ eqi eqs => exact eqi ▸ eqs ▸ path₂
  | step step _ ih => exact .step step (ih path₂)

def pathToNext (nfa : NFA) (next start i : Nat) (cs cs' : List Char) : Prop :=
  ∃ (i' : Nat) (cs'' : List Char),
    nfa.pathIn start i cs i' cs'' ∧
    nfa.stepIn start i' cs'' next cs'

theorem le_of_pathToNext {start} (path : pathToNext nfa next start i cs cs') : start ≤ i := by
  obtain ⟨_, _, path, _⟩ := path
  exact le_of_pathIn_left path

theorem pathToNext.cons {start} {cs cs' cs'' : List Char}
  (step : stepIn nfa start i cs j cs') (path : pathToNext nfa next start j cs' cs'') :
  pathToNext nfa next start i cs cs'' := by
  obtain ⟨i', cs''', path, step'⟩ := path
  exact ⟨i', cs''', .step step path, step'⟩

theorem pathToNext.cast {nfa nfa' : NFA} {next start i : Nat} {cs cs' : List Char}
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → ∃ h' : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : pathToNext nfa next start i cs cs') :
  pathToNext nfa' next start i cs cs' := by
  obtain ⟨i', cs'', path, step⟩ := path
  obtain ⟨h', eq'⟩ := eq _ (le_of_pathIn_right path) step.h₂
  exact ⟨i', cs'', pathIn.cast start eq path, step.cast h' eq'⟩

theorem pathToNext.cast' {nfa nfa' : NFA} {start : Nat}
  (assm : i < nfa.nodes.size) (le : nfa.nodes.size ≤ nfa'.nodes.size)
  (eq : ∀ i, (h₁ : start ≤ i) → (h₂ : i < nfa.nodes.size) → nfa[i] = nfa'[i]'(Nat.lt_of_lt_of_le h₂ le))
  (path : pathToNext nfa' next start i cs cs') :
  pathToNext nfa next start i cs cs' := by
  obtain ⟨i', cs'', path, step⟩ := path
  have path' := path.cast' assm le eq
  have lt : i' < nfa.nodes.size := path'.lt_right assm
  exact ⟨i', cs'', path', step.cast lt (eq i' step.h₁ lt).symm⟩

theorem pathToNext.castStart {nfa : NFA} {start start' : Nat} {i : Nat} {cs cs' : List Char}
  (le : start' ≤ start) (path : pathToNext nfa next start i cs cs') :
  pathToNext nfa next start' i cs cs' := by
  obtain ⟨i', cs'', path, step⟩ := path
  exact ⟨i', cs'', path.castStart le, step.castStart le⟩

theorem pathToNext.castLE {nfa : NFA} {next start start' i : Nat} {cs cs' : List Char}
  (assm : start' ≤ i)
  (inBounds : ∀ i j, (h₁ : start' ≤ i) →
    (h₂ : i < nfa.nodes.size) →
    (∃ c, j ∈ nfa[i].charStep c) ∨ j ∈ nfa[i].εStep →
    start ≤ j →
    start' ≤ j)
  (path : pathToNext nfa next start i cs cs') :
  pathToNext nfa next start' i cs cs' := by
  obtain ⟨i', cs'', path, step⟩ := path
  have path' := path.castLE assm inBounds
  exact ⟨i', cs'', path', step.castStart' (le_of_pathIn_right path')⟩

theorem pathToNext.trans {nfa : NFA} {start : Nat} {cs cs' cs'' : List Char}
  (path₁ : pathToNext nfa j start i cs cs') (path₂ : pathToNext nfa k start j cs' cs'') :
  pathToNext nfa k start i cs cs'' := by
  obtain ⟨i', cs''', path₁, step₁⟩ := path₁
  obtain ⟨j', cs'''', path₂, step₂⟩ := path₂
  exact ⟨j', cs'''', path₁.trans (.step step₁ path₂), step₂⟩

end NFA
