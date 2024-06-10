-- When the compiled NFA accepts a string, the regex matches it.
import RegexCorrectness.NFA.Transition.Basic

namespace NFA

theorem eq_next_of_pathToNext (eq : pushRegex nfa next r = result)
  (assm : next' < nfa.nodes.size)
  (path : pathToNext result next' nfa.nodes.size i cs) :
  next' = next := by
  obtain ⟨i', pcs, scs, _, path, step⟩ := path
  have := eq_or_ge_of_step_pushRegex eq (le_of_pathIn_right path) step.h₂ step.step
  cases this with
  | inl eq => exact eq
  | inr ge => exfalso; exact Nat.not_le_of_lt assm ge

theorem pathIn_split {start : Nat} (eq : pushRegex nfa next r = result)
  (assm₁ : i' < nfa.nodes.size) (assm₂ : nfa.nodes.size ≤ i)
  (path : pathIn result start i i' cs) :
  ∃ cs₁ cs₂,
    cs = cs₁ ++ cs₂ ∧
    pathToNext result next nfa.nodes.size i cs₁ ∧
    pathIn result start next i' cs₂ := by
  induction path with
  | base _ => exact absurd assm₁ (Nat.not_lt_of_le assm₂)
  | @step i j k cs cs' step rest ih =>
    have := eq_or_ge_of_step_pushRegex eq assm₂ step.h₂ step.step
    cases this with
    | inl eq =>
      simp [eq] at step rest
      have pathToNext : pathToNext result next nfa.nodes.size i cs :=
        ⟨i, [], cs, rfl, .base assm₂, step.castStart' assm₂⟩
      exact ⟨cs, cs', rfl, pathToNext, rest⟩
    | inr ge =>
      obtain ⟨cs₁, cs₂, eqs, pathToNext, pathIn⟩ := ih assm₁ ge
      exact ⟨cs ++ cs₁, cs₂, by simp [eqs], pathToNext.cons (step.castStart' assm₂), pathIn⟩

theorem rStart_of_push_star (eq : pushRegex nfa next (.star r) = result) :
  ∃ rStart, nfa.nodes.size + 1 ≤ rStart ∧ result.val[nfa.nodes.size]'result.property = .split rStart next := by
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq
  exists compiled.val.start
  simp [eq, eq₄, get_eq_nodes_get, eq₃]
  have := ge_pushRegex_start eq₂.symm
  simp [eq₁] at this
  exact this

-- NOTE: we can redo the compilation to compute the start position pedantically, but I don't care
noncomputable def rStart_of (eq : pushRegex nfa next (.star r) = result) : Nat :=
  Exists.choose (rStart_of_push_star eq)

theorem rStart_of_spec (eq : pushRegex nfa next (.star r) = result) :
  nfa.nodes.size + 1 ≤ (rStart_of eq) ∧ result.val[nfa.nodes.size]'result.property = .split (rStart_of eq) next :=
  (rStart_of_push_star eq).choose_spec

inductive starLoop (eq : pushRegex nfa next (.star r) = result) : List Char → Prop where
  | complete : starLoop eq []
  | loop
    (path : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) (rStart_of eq) cs₁)
    (rest : starLoop eq cs₂) : starLoop eq (cs₁ ++ cs₂)

theorem starLoop.intro' (eq : pushRegex nfa next (.star r) = result)
  (assm₁ : i < result.val.nodes.size) (assm₂ : loopStart = nfa.nodes.size)
  (ev : pathIn result nfa.nodes.size i loopStart cs) :
  if i = nfa.nodes.size then
    (cs = []) ∨
    (∃ cs₁ cs₂,
      cs = cs₁ ++ cs₂ ∧
      pathToNext result nfa.nodes.size (nfa.nodes.size + 1) (rStart_of eq) cs₁ ∧
      starLoop eq cs₂)
  else
    ∃ cs₁ cs₂,
      cs = cs₁ ++ cs₂ ∧
      pathToNext result nfa.nodes.size (nfa.nodes.size + 1) i cs₁ ∧
      starLoop eq cs₂ := by
  induction ev with
  | base h =>
    subst assm₂
    simp
  | @step i j k cs cs' step path ih =>
    have ih := ih step.lt_right assm₂
    split
    case inl eqi =>
      subst eqi
      have ⟨ge, node⟩ := rStart_of_spec eq
      simp [node]
      cases step with
      | charStep _ _ step => simp [node, NFA.Node.charStep] at step
      | εStep h₁ h₂ step =>
        apply Or.inr
        have : j = rStart_of eq := by
          simp [node, NFA.Node.εStep] at step
          cases step with
          | inl eq => exact eq
          | inr eq =>
            have : nfa.nodes.size ≤ j := le_of_pathIn_left path
            exact absurd next.isLt (Nat.not_lt_of_le (eq ▸ this))
        subst this
        simp [NFA.Node.εStep]
        have : rStart_of eq ≠ nfa.nodes.size := Nat.ne_of_gt ge
        simp [this] at ih
        exact ih
    case inr nei =>
      have gti : nfa.nodes.size < i := Nat.lt_of_le_of_ne step.h₁ (Ne.symm nei)
      split at ih
      case inl eqj =>
        have toNext : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) i cs :=
          ⟨i, [], cs, rfl, .base gti, (eqj ▸ step).castStart' gti⟩
        cases ih with
        | inl eqs =>
          subst eqs
          exact ⟨cs, [], rfl, toNext, .complete⟩
        | inr cond =>
          obtain ⟨cs₁, cs₂, eqs, path', loop⟩ := cond
          exact ⟨cs, cs₁ ++ cs₂, by simp [eqs], toNext, .loop path' loop⟩
      case inr nej =>
        obtain ⟨cs₁, cs₂, eqs, path', loop⟩ := ih
        subst eqs
        cases step with
        | charStep h₁ h₂ step =>
          exact ⟨_ :: cs₁, cs₂, rfl, path'.cons (.charStep gti h₂ step), loop⟩
        | εStep h₁ h₂ step =>
          exact ⟨cs₁, cs₂, rfl, path'.cons (.εStep gti h₂ step), loop⟩

theorem starLoop.intro (eq : pushRegex nfa next (.star r) = result)
  (ev : pathIn result nfa.nodes.size nfa.nodes.size nfa.nodes.size cs) :
  starLoop eq cs := by
  let loop := starLoop.intro' eq result.property rfl ev
  simp at loop
  match loop with
  | .inl eqs => exact eqs ▸ .complete
  | .inr ⟨cs₁, cs₂, eqs, path, loop⟩ =>
    exact eqs ▸ .loop path loop

theorem matches_of_starLoop (eq : pushRegex nfa next (.star r) = result)
  (mr : ∀ {cs},
    pathToNext result (Array.size nfa.nodes) (Array.size nfa.nodes + 1) (rStart_of eq) cs →
    r.matches cs)
  (loop : starLoop eq cs) :
  (Regex.star r).matches cs := by
  induction loop with
  | complete => exact .starEpsilon
  | loop path _ m₂ => exact .starConcat _ _ _ (mr path) m₂

theorem matches_of_path.group (eq : pushRegex nfa next (.group i r) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val cs)
  (ih : ∀ {nfa next result cs},
    pushRegex nfa next r = result →
    pathToNext result next nfa.nodes.size result.val.start.val cs →
    r.matches cs) :
  (Regex.group i r).matches cs := by
  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property _ _ eq₁ eq₂ eq₃ eq

  suffices pathToNext nfa'' nfa'.val.start nfa'.val.nodes.size nfa''.val.start cs from
    .group (ih eq₂.symm this)

  rw [eq] at path
  simp at path

  obtain ⟨i', cs₁, cs₂, eqs, path, step⟩ := path
  have heq : i' = nfa.nodes.size ∧ cs₂ = [] := by
    cases Nat.eq_or_lt_of_le (le_of_pathIn_right path) with
    | inl eq =>
      have eqStart : nfa'''.val[nfa.nodes.size] = .save (2 * i + 1) next := by
        simp [eq₃]
        rw [pushNode_get_lt _ (Nat.lt_trans nfa'.property nfa''.property)]
        rw [pushRegex_get_lt eq₂.symm _ nfa'.property]
        simp [eq₁]
      rw [←eq] at step
      cases step with
      | charStep _ _ step =>
        rw [eqStart] at step
        simp [Node.charStep] at step
      | εStep _ _ eqs => exact ⟨eq.symm, rfl⟩
    | inr gt =>
      apply False.elim
      cases Nat.lt_or_ge i' nfa''.val.nodes.size with
      | inl lt =>
        have h₁ : nfa'.val.nodes.size ≤ i' := by
          simp [eq₁]
          exact gt
        have : i' < nfa'''.val.nodes.size := Nat.lt_trans lt nfa'''.property
        have : nfa'''.val[i'] = nfa''.val[i'] := by
          simp [eq₃]
          rw [pushNode_get_lt _ lt]
        have := eq_or_ge_of_step_pushRegex eq₂.symm h₁ lt (step.cast lt this).step
        cases this with
        | inl eq =>
          rw [eq₁] at eq
          simp at eq
          exact Nat.lt_irrefl _ (eq ▸ next.isLt)
        | inr ge => exact Nat.lt_irrefl _ (Nat.lt_of_lt_of_le (Nat.lt_trans next.isLt nfa'.property) ge)
      | inr ge =>
        have eqStart : nfa'''.val[nfa''.val.nodes.size]'nfa'''.property = .save (2 * i) nfa''.val.start := by
          simp [eq₃]
        have h₂ := step.h₂
        simp [eq₃] at h₂
        have : i' = nfa''.val.nodes.size := Nat.eq_of_ge_of_lt ge h₂
        have step := step.step
        simp [this, eqStart, Node.charStep, Node.εStep] at step
        have : nfa.nodes.size < nfa''.val.start := Nat.lt_of_lt_of_le nfa'.property (ge_pushRegex_start eq₂.symm)
        exact Nat.lt_irrefl _ (Nat.lt_trans (step ▸ this) next.isLt)

  cases path with
  | base _ =>
    rw [eq₃] at heq
    simp at heq
    have : nfa.nodes.size < nfa''.val.nodes.size := Nat.lt_trans nfa'.property nfa''.property
    exact (Nat.lt_irrefl _ (heq.left ▸ this)).elim
  | @step _ j _ cs₁ cs₂ step' rest =>
    simp [eqs, heq.right]
    have eqStart : nfa'''.val[nfa'''.val.start.val] = .save (2 * i) nfa''.val.start := by
      rw [eq₃]
      simp
    cases step' with
    | charStep _ _ step => simp [eqStart, Node.charStep] at step
    | εStep _ _ step =>
      simp [eqStart, Node.εStep] at step
      subst step
      simp
      have : pathIn nfa'' nfa.nodes.size nfa''.val.start i' cs₂ := by
        apply rest.cast' (nfa''.val.start.isLt) (Nat.le_of_lt nfa'''.property)
        intro i _ h₂
        rw [eq₃, pushNode_get_lt _ h₂]
      have ⟨cs₃, cs₄, eqs, path', path''⟩ :=
        pathIn_split eq₂.symm (heq.left ▸ nfa'.property) (ge_pushRegex_start eq₂.symm) this
      cases path'' with
      | base _ =>
        simp at eqs
        exact eqs ▸ path'
      | step step rest =>
        have : nfa'.val.start.val < nfa''.val.nodes.size :=
          Nat.lt_trans nfa'.val.start.isLt nfa''.property
        have eqStart : nfa''.val[nfa'.val.start.val] = .save (2 * i + 1) next := by
          rw [pushRegex_get_lt eq₂.symm _ nfa'.val.start.isLt]
          rw [eq₁]
          simp
        have step := step.step
        simp [eqStart, Node.charStep, Node.εStep] at step
        subst step
        have := le_of_pathIn_left rest
        exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this next.isLt)).elim

theorem matches_of_path.alternate (eq : pushRegex nfa next (.alternate r₁ r₂) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val cs)
  (ih₁ : ∀ {nfa next result cs},
    pushRegex nfa next r₁ = result →
    pathToNext result next nfa.nodes.size result.val.start.val cs →
    r₁.matches cs)
  (ih₂ : ∀ {nfa next result cs},
    pushRegex nfa next r₂ = result →
    pathToNext result next nfa.nodes.size result.val.start.val cs →
    r₂.matches cs) :
  (Regex.alternate r₁ r₂).matches cs := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ inBounds final property eq₁ eq₂ eq₃ eq₄ eq₅ eq'

  rw [eq'] at path
  simp at path

  have startNode : final.val[final.val.start.val] = .split start₁ start₂ := by
    rw [eq₅]
    simp
  have neStart₁ : next.val ≠ start₁.val := by
    apply Nat.ne_of_lt
    apply Nat.lt_of_lt_of_le next.isLt
    exact eq₂ ▸ ge_pushRegex_start eq₁.symm
  have neStart₂ : next.val ≠ start₂.val := by
    apply Nat.ne_of_lt
    apply Nat.lt_of_lt_of_le (Nat.lt_trans next.isLt nfa₁.property)
    exact eq₄ ▸ ge_pushRegex_start eq₃.symm

  have get₂ (i : Nat) (_ : nfa.nodes.size ≤ i) (h₂: i < nfa₂.val.nodes.size) :
    nfa₂.val[i] = final.val[i]'(Nat.lt_trans h₂ final.property) := by
    simp [eq₅]
    rw [pushNode_get_lt]

  have get₁ (i : Nat) (h₁ : nfa.nodes.size ≤ i) (h₂: i < nfa₁.val.nodes.size) :
    nfa₁.val[i] = final.val[i]'(Nat.lt_trans (Nat.lt_trans h₂ nfa₂.property) final.property) := by
    rw [←get₂ i h₁ (Nat.lt_trans h₂ nfa₂.property)]
    rw [pushRegex_get_lt eq₃.symm]

  obtain ⟨i, cs₁, cs₂, eqs, path, step⟩ := path
  cases path with
  | base _ =>
    cases step with
    | charStep _ _ step => simp [NFA.Node.charStep, startNode] at step
    | εStep _ _ step =>
      simp [NFA.Node.εStep, startNode] at step
      cases step <;> simp only [neStart₁, neStart₂] at *
  | @step _ _ _ cs₃ cs₄ step rest =>
    cases step with
    | charStep _ _ step => simp [NFA.Node.charStep, startNode] at step
    | εStep _ _ step =>
      simp at eqs
      simp [NFA.Node.εStep, startNode] at step
      cases step with
      | inl eqs₁ =>
        rw [eqs₁] at rest
        have : pathToNext final next nfa.nodes.size nfa₁.val.start.val cs :=
          ⟨i, cs₄, cs₂, eqs, eq₂ ▸ rest, step⟩
        have : pathToNext nfa₁ next nfa.nodes.size nfa₁.val.start.val cs := by
          apply this.cast' nfa₁.val.start.isLt
            (Nat.le_of_lt (Nat.lt_trans nfa₂.property final.property))
            get₁
        exact .alternateLeft (ih₁ eq₁.symm this)
      | inr eqs₂ =>
        rw [eqs₂] at rest
        have : pathToNext final next nfa.nodes.size nfa₂.val.start.val cs :=
          ⟨i, cs₄, cs₂, eqs, eq₄ ▸ rest, step⟩
        have : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start.val cs := by
          apply this.cast' nfa₂.val.start.isLt (Nat.le_of_lt final.property) get₂
        have : pathToNext nfa₂ next nfa₁.val.nodes.size nfa₂.val.start.val cs := by
          apply this.castLE (ge_pushRegex_start eq₃.symm)

          intro i j h₁ h₂ step hj
          have := eq_or_ge_of_step_pushRegex eq₃.symm h₁ h₂ step
          simp at this
          cases this with
          | inl eq =>
            exfalso
            rw [eq] at hj
            exact Nat.not_le_of_gt next.isLt hj
          | inr ge => exact ge
        exact .alternateRight (ih₂ eq₃.symm this)

theorem matches_of_path.concat (eq : pushRegex nfa next (.concat r₁ r₂) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val cs)
  (ih₁ : ∀ {nfa next result cs},
    pushRegex nfa next r₁ = result →
    pathToNext result next nfa.nodes.size result.val.start.val cs →
    r₁.matches cs)
  (ih₂ : ∀ {nfa next result cs},
    pushRegex nfa next r₂ = result →
    pathToNext result next nfa.nodes.size result.val.start.val cs →
    r₂.matches cs) :
  (Regex.concat r₁ r₂).matches cs := by
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq'

  rw [eq'] at path
  simp at path

  have get (i : Nat) (_ : Array.size nfa.nodes ≤ i) (h₂ : i < nfa₂.val.nodes.size) :
    nfa₂.val[i] = nfa₁.val[i]'(Nat.lt_trans h₂ nfa₁.property) := by
    rw [pushRegex_get_lt eq₁.symm]

  obtain ⟨i, cs₁, cs₂, eqs, path, step₂⟩ := path
  have lti : i < nfa₂.val.nodes.size := by
    by_contra nlt
    apply Nat.lt_irrefl next
    have := eq_or_ge_of_step_pushRegex eq₁.symm (Nat.le_of_not_lt nlt) step₂.h₂ step₂.step
    cases this with
    | inl eq =>
      have := ge_pushRegex_start eq₂.symm
      calc
        _ < nfa.nodes.size := next.isLt
        _ ≤ nfa₂.val.start := this
        _ = next := eq.symm
    | inr ge =>
      calc
        _ < nfa.nodes.size := next.isLt
        _ < nfa₂.val.nodes.size := nfa₂.property
        _ ≤ next := ge
  have ⟨cs₃, cs₄, eqs', path₁, path₂⟩ :=
    pathIn_split eq₁.symm lti (ge_pushRegex_start eq₁.symm) path
  have m₁ := ih₁ eq₁.symm path₁
  have path₂ : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start.val (cs₄ ++ cs₂) := by
    have step₂ : stepIn nfa₂ nfa.nodes.size i next cs₂ := by
      apply step₂.cast lti
      rw [get i step₂.h₁ lti]
    refine ⟨i, cs₄, cs₂, rfl, ?_, step₂⟩
    apply path₂.cast' nfa₂.val.start.isLt (Nat.le_of_lt nfa₁.property) get
  have m₂ := ih₂ eq₂.symm path₂

  simp [eqs, eqs']
  exact .concat _ _ _ _ m₁ m₂

theorem matches_of_path.star (eq : pushRegex nfa next (.star r) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val cs)
  (ih : ∀ {nfa next result cs},
    pushRegex nfa next r = result →
    pathToNext result next nfa.nodes.size result.val.start.val cs →
    Regex.matches cs r) :
  (Regex.star r).matches cs := by
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq'

  obtain ⟨i, cs₁, cs₂, eqs, path, step⟩ := path
  have eqis := eq_of_step_next eq step
  simp [eqis] at path
  simp [eqis] at step eqs
  simp [eqs]
  have loop : starLoop eq cs₁ := by
    apply starLoop.intro eq
    suffices result.val.start = nfa.nodes.size by
      rw [this] at path
      exact path
    rw [eq']
    simp
    rw [eq₄]
  apply matches_of_starLoop eq ?_ loop

  intro cs path'
  apply ih eq₂.symm
  simp [eq₁]

  have ⟨_, mem⟩ := rStart_of_spec eq
  have : compiled.val.start.val = rStart_of eq := by
    have : result.val[nfa.nodes.size]'result.property = .split compiled.val.start.val next := by
      simp [eq', eq₄, get_eq_nodes_get, eq₃]
    simp [this] at mem
    exact mem
  rw [this]
  apply path'.cast

  intro j h₁ h₂
  simp [eq', eq₄, eq₃] at h₂
  exists h₂

  simp [eq', get_eq_nodes_get, eq₄]
  simp [eq₃]
  rw [Array.get_set_ne]
  simp
  exact Nat.ne_of_lt h₁
where
  eq_of_step_next {i cs} (eq : pushRegex nfa next (.star r) = result)
    (step : stepIn result nfa.nodes.size i next cs) :
    i = nfa.nodes.size ∧ cs = [] := by
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      eq₁ eq₂ eq₃ eq₄ eq'

    cases Nat.lt_or_ge i (nfa.nodes.size + 1) with
    | inl lt =>
      have eqi := Nat.eq_of_ge_of_lt step.h₁ lt
      obtain ⟨_, node⟩ := rStart_of_spec eq
      cases step with
      | charStep _ _ step => simp [eqi, node, NFA.Node.charStep] at step
      | εStep _ _ step => simp [eqi]
    | inr ge =>
      exfalso
      have eqs : placeholder.val.nodes.size = nfa.nodes.size + 1 := by
        simp [eq₁]
      have h₂ : i < compiled.val.nodes.size := by
        have := step.h₂
        simp [eq', eq₄, eq₃] at this
        exact this
      have eqn : result.val[i]'step.h₂ = compiled.val[i] := by
        simp [eq', get_eq_nodes_get, eq₄]
        simp [eq₃]
        rw [Array.get_set_ne]
        simp
        exact Nat.ne_of_lt ge
      have := eq_or_ge_of_step_pushRegex eq₂.symm (eqs ▸ ge) h₂ (eqn ▸ step.step)
      simp [eqs] at this
      cases this with
      | inl eq => exact Nat.lt_irrefl _ (eq ▸ next.isLt)
      | inr gt => exact Nat.lt_irrefl _ (Nat.lt_trans gt next.isLt)

theorem List.concat_eq_append {α} {c : α} (l₂ : List α) : [c] ++ l₂ = c :: l₂ := rfl

theorem matches_of_pathToNext_pushRegex
  (eq : pushRegex nfa next r = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val cs) :
  r.matches cs := by
  induction r generalizing nfa next cs with
  | classes cls =>
    apply pushRegex.sparse eq
    intro eq
    rw [eq] at path
    obtain ⟨i, pcs, scs, eqs, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    match step with
    | stepIn.charStep (c := c) _ _ step =>
      simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
      cases path with
      | base _ =>
        simp [eqs]
        exact .sparse cls c step
      | step step rest =>
        cases step with
        | charStep _ _ step =>
          simp [NFA.Node.charStep] at step
          have := le_of_pathIn_left rest
          exact absurd next.isLt (Nat.not_lt_of_ge (step.right ▸ this))
        | εStep _ _ step => simp [NFA.Node.εStep] at step
    | stepIn.εStep _ _ step =>
        simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
  | empty =>
    apply pushRegex.empty eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, _, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
  | epsilon =>
    apply pushRegex.epsilon eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, _, eqs, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
    cases path with
    | base _ => exact eqs ▸ .epsilon
    | step step rest =>
      cases step with
      | charStep _ _ step => simp [NFA.Node.charStep] at step
      | εStep _ _ step =>
        simp [NFA.Node.εStep] at step
        have := le_of_pathIn_left rest
        exact absurd next.isLt (Nat.not_lt_of_ge (step ▸ this))
  | char c =>
    apply pushRegex.char eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, _, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
    cases path with
    | base _ =>
      simp [*]
      exact .char c
    | step step rest =>
      cases step with
      | charStep _ _ step =>
        simp [NFA.Node.charStep] at step
        have := le_of_pathIn_left rest
        exact absurd next.isLt (Nat.not_lt_of_ge (step.right ▸ this))
      | εStep _ _ step => simp [NFA.Node.εStep] at step
  | group i r ih => exact matches_of_path.group eq path ih
  | alternate r₁ r₂ ih₁ ih₂ => exact matches_of_path.alternate eq path ih₁ ih₂
  | concat r₁ r₂ ih₁ ih₂ => exact matches_of_path.concat eq path ih₁ ih₂
  | star r ih => exact matches_of_path.star eq path ih

theorem matches_of_pathToNext_compile (eq : NFA.compile r = nfa)
  (path : pathToNext nfa 0 1 nfa.start.val cs) :
  r.matches cs := by
  set result := NFA.done.pushRegex ⟨0, by decide⟩ r
  have : nfa = result.val := by
    rw [←eq]
    rfl
  rw [this] at path
  exact matches_of_pathToNext_pushRegex rfl path

end NFA
