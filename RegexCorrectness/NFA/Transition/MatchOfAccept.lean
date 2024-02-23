-- When the compiled NFA accepts a prefix, the regex matches it.
import RegexCorrectness.NFA.Transition.Basic

namespace NFA

theorem eq_next_of_pathToNext (eq : pushRegex nfa next r = result)
  (assm : next' < nfa.nodes.size)
  (path : pathToNext result next' nfa.nodes.size i cs cs') :
  next' = next := by
  obtain ⟨i', cs'', path, step⟩ := path
  have := eq_or_ge_of_step_pushRegex eq (le_of_pathIn_right path) step.h₂ step.step
  cases this with
  | inl eq => exact eq
  | inr ge => exfalso; exact Nat.not_le_of_lt assm ge

theorem pathIn_split {start : Nat} (eq : pushRegex nfa next r = result)
  (assm₁ : start < nfa.nodes.size) (assm₂ : i' < nfa.nodes.size) (assm₃ : nfa.nodes.size ≤ i)
  (path : pathIn result start i cs i' cs') :
  ∃ cs'', pathToNext result next nfa.nodes.size i cs cs'' ∧
    pathIn result start next cs'' i' cs' := by
  induction path with
  | base _ eqi => exact absurd assm₂ (Nat.not_lt_of_le (eqi ▸ assm₃))
  | @step i j k cs cs' cs'' step rest ih =>
    have := eq_or_ge_of_step_pushRegex eq assm₃ step.h₂ step.step
    cases this with
    | inl eq =>
      simp [eq] at step rest
      have pathToNext : pathToNext result next nfa.nodes.size i cs cs' :=
        ⟨i, cs, .base assm₃ rfl rfl, step.castStart' assm₃⟩
      exact ⟨cs', pathToNext, rest⟩
    | inr ge =>
      obtain ⟨cs''', pathToNext, pathIn⟩ := ih assm₂ ge
      exact ⟨cs''', pathToNext.cons (step.castStart' assm₃), pathIn⟩

inductive starLoop (eq : pushRegex nfa next (.star r) = result) : List Char → List Char → Prop where
  | complete (eqs : cs = cs') : starLoop eq cs cs'
  | loop (mem : rStart ∈ (result.val[nfa.nodes.size]'result.property).εStep)
    (path : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) rStart cs cs'')
    (rest : starLoop eq cs'' cs') : starLoop eq cs cs'

theorem rStart_of_push_star (eq : pushRegex nfa next (.star r) = result) :
  ∃ rStart, nfa.nodes.size + 1 ≤ rStart ∧ result.val[nfa.nodes.size]'result.property = .split rStart next := by
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq
  exists compiled.val.start
  simp [eq, eq₄, get_eq_nodes_get]
  simp [eq₃]
  rw [Array.get_set_eq]
  simp
  have := ge_pushRegex_start eq₂.symm
  simp [eq₁] at this
  exact this

theorem starLoop.intro' (eq : pushRegex nfa next (.star r) = result)
  (assm₁ : i < result.val.nodes.size) (assm₂ : loopStart = nfa.nodes.size)
  (ev : pathIn result nfa.nodes.size i cs loopStart cs') :
  if i = nfa.nodes.size then
    (cs = cs') ∨
    (∃ j cs'', j ∈ result.val[i].εStep ∧
    pathToNext result nfa.nodes.size (nfa.nodes.size + 1) j cs cs'' ∧ starLoop eq cs'' cs')
  else
    ∃ cs'', pathToNext result nfa.nodes.size (nfa.nodes.size + 1) i cs cs'' ∧ starLoop eq cs'' cs' := by
  induction ev with
  | base h eqi eqs =>
    subst eqi assm₂
    simp
    exact .inl eqs
  | @step i j k cs cs'' cs' step path ih =>
    have ih := ih step.lt_right assm₂
    split
    case inl eqi =>
      subst eqi
      obtain ⟨rStart, ge, node⟩ := rStart_of_push_star eq
      simp [node]
      cases step with
      | charStep _ _ step => simp [node, NFA.Node.charStep] at step
      | εStep h₁ h₂ step =>
        refine .inr ⟨j, ?_⟩
        have : j = rStart := by
          simp [node, NFA.Node.εStep] at step
          cases step with
          | inl eq => exact eq
          | inr eq =>
            have : nfa.nodes.size ≤ j := le_of_pathIn_left path
            exact absurd next.isLt (Nat.not_lt_of_le (eq ▸ this))
        subst this
        simp [NFA.Node.εStep]
        have : j ≠ nfa.nodes.size := Nat.ne_of_gt ge
        simp [this] at ih
        exact ih
    case inr nei =>
      have gti : nfa.nodes.size < i := Nat.lt_of_le_of_ne step.h₁ (Ne.symm nei)
      split at ih
      case inl eqj =>
        have toNext : pathToNext result nfa.nodes.size (nfa.nodes.size + 1) i cs cs'' :=
          ⟨i, cs, .base gti rfl rfl, (eqj ▸ step).castStart' gti⟩
        cases ih with
        | inl eqs =>
          exists cs''
          exact ⟨toNext, .complete eqs⟩
        | inr cond =>
          match cond with
          | ⟨j', cs''', step, path', l⟩ =>
            exact ⟨cs'', toNext, .loop (eqj ▸ step) path' l⟩
      case inr nej =>
        obtain ⟨cs'', path, loop⟩ := ih
        exact ⟨cs'', path.cons (step.castStart' gti), loop⟩

theorem starLoop.intro (eq : pushRegex nfa next (.star r) = result)
  (ev : pathIn result nfa.nodes.size nfa.nodes.size cs nfa.nodes.size cs') :
  starLoop eq cs cs' := by
  let loop := starLoop.intro' eq result.property rfl ev
  simp at loop
  match loop with
  | .inl eqs => exact .complete eqs
  | .inr ⟨rStart, step, _, path, loop⟩ => exact .loop step path loop

theorem matches_prefix_of_starLoop (eq : pushRegex nfa next (.star r) = result)
  (mr : ∀ {cs cs'} rStart,
    rStart ∈ (result.val[nfa.nodes.size]'result.property).εStep →
    pathToNext result (Array.size nfa.nodes) (Array.size nfa.nodes + 1) rStart cs cs' →
    ∃ p, cs = p ++ cs' ∧ r.matches ⟨p⟩)
  (loop : starLoop eq cs cs') :
  ∃ p, cs = p ++ cs' ∧ (Regex.star r).matches ⟨p⟩ := by
  induction loop with
  | complete eqs => exact ⟨[], eqs, .starEpsilon rfl⟩
  | loop mem path _ ih =>
    let ⟨p₁, eqs₁, m₁⟩ := mr _ mem path
    let ⟨p₂, eqs₂, m₂⟩ := ih
    exact ⟨p₁ ++ p₂, by simp [eqs₁, eqs₂], .starConcat _ _ _ _ rfl m₁ m₂⟩

theorem matches_prefix_of_path.group (eq : pushRegex nfa next (.group i r) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val s s')
  (ih : ∀ {nfa next result s s'},
    pushRegex nfa next r = result →
    pathToNext result next nfa.nodes.size result.val.start.val s s' →
    ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩) :
  ∃ p, s = p ++ s' ∧ (Regex.group i r).matches ⟨p⟩ := by
  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property _ _ eq₁ eq₂ eq₃ eq

  suffices pathToNext nfa'' nfa'.val.start nfa'.val.nodes.size nfa''.val.start s s' by
    have ⟨p, eqs, m⟩ := ih eq₂.symm this
    exact ⟨p, eqs, .group m⟩

  rw [eq] at path
  simp at path

  obtain ⟨i', s'', path, step⟩ := path
  have : i' = nfa.nodes.size ∧ s' = s'' := by
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
  have : i' = nfa.nodes.size := this.left
  subst this
  have : s' = s'' := this.right
  subst this

  cases path with
  | base _ eqi =>
    rw [eq₃] at eqi
    simp at eqi
    have : nfa.nodes.size < nfa''.val.nodes.size := Nat.lt_trans nfa'.property nfa''.property
    apply False.elim (Nat.lt_irrefl _ (eqi ▸ this))
  | step step rest =>
    have eqStart : nfa'''.val[nfa'''.val.start.val] = .save (2 * i) nfa''.val.start := by
      rw [eq₃]
      simp
    cases step with
    | charStep _ _ step => simp [eqStart, Node.charStep] at step
    | εStep _ _ step =>
      simp [eqStart, Node.εStep] at step
      subst step
      have : pathIn nfa'' nfa.nodes.size nfa''.val.start s nfa.nodes.size s' := by
        apply rest.cast' nfa''.val.start.isLt (Nat.le_of_lt nfa'''.property)
        intro i _ h₂
        rw [eq₃, pushNode_get_lt _ h₂]
      have ⟨s'', path', path''⟩ := pathIn_split eq₂.symm nfa'.property nfa'.property (ge_pushRegex_start eq₂.symm) this
      cases path'' with
      | base _ _ eqs => exact eqs ▸ path'
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
        exact False.elim (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this next.isLt))

theorem matches_prefix_of_path.alternate (eq : pushRegex nfa next (.alternate r₁ r₂) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val s s')
  (ih₁ : ∀ {nfa next result s s'},
    pushRegex nfa next r₁ = result →
    pathToNext result next nfa.nodes.size result.val.start.val s s' →
    ∃ p, s = p ++ s' ∧ r₁.matches ⟨p⟩)
  (ih₂ : ∀ {nfa next result s s'},
    pushRegex nfa next r₂ = result →
    pathToNext result next nfa.nodes.size result.val.start.val s s' →
    ∃ p, s = p ++ s' ∧ r₂.matches ⟨p⟩) :
  ∃ p, s = p ++ s' ∧ (Regex.alternate r₁ r₂).matches ⟨p⟩ := by
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

  obtain ⟨i, s'', path, step⟩ := path
  cases path with
  | base _ eqi =>
    rw [←eqi] at step
    cases step with
    | charStep _ _ step => simp [NFA.Node.charStep, startNode] at step
    | εStep _ _ step =>
      simp [NFA.Node.εStep, startNode] at step
      cases step <;> simp only [neStart₁, neStart₂] at *
  | step step rest =>
    cases step with
    | charStep _ _ step => simp [NFA.Node.charStep, startNode] at step
    | εStep _ _ step =>
      simp [NFA.Node.εStep, startNode] at step
      cases step with
      | inl eqs₁ =>
        rw [eqs₁] at rest
        have : pathToNext final next nfa.nodes.size nfa₁.val.start.val s s' :=
          ⟨i, s'', eq₂ ▸ rest, step⟩
        have : pathToNext nfa₁ next nfa.nodes.size nfa₁.val.start.val s s' := by
          apply this.cast' nfa₁.val.start.isLt
            (Nat.le_of_lt (Nat.lt_trans nfa₂.property final.property))
            get₁
        obtain ⟨p, eqs, m₁⟩ := ih₁ eq₁.symm this
        exact ⟨p, eqs, .alternateLeft m₁⟩
      | inr eqs₂ =>
        rw [eqs₂] at rest
        have : pathToNext final next nfa.nodes.size nfa₂.val.start.val s s' :=
          ⟨i, s'', eq₄ ▸ rest, step⟩
        have : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start.val s s' := by
          apply this.cast' nfa₂.val.start.isLt (Nat.le_of_lt final.property) get₂
        have : pathToNext nfa₂ next nfa₁.val.nodes.size nfa₂.val.start.val s s' := by
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
        obtain ⟨p, eqs, m₂⟩ := ih₂ eq₃.symm this
        exact ⟨p, eqs, .alternateRight m₂⟩

theorem matches_prefix_of_path.concat (eq : pushRegex nfa next (.concat r₁ r₂) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val s s')
  (ih₁ : ∀ {nfa next result s s'},
    pushRegex nfa next r₁ = result →
    pathToNext result next nfa.nodes.size result.val.start.val s s' →
    ∃ p, s = p ++ s' ∧ r₁.matches ⟨p⟩)
  (ih₂ : ∀ {nfa next result s s'},
    pushRegex nfa next r₂ = result →
    pathToNext result next nfa.nodes.size result.val.start.val s s' →
    ∃ p, s = p ++ s' ∧ r₂.matches ⟨p⟩) :
  ∃ p, s = p ++ s' ∧ (Regex.concat r₁ r₂).matches ⟨p⟩ := by
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq'

  rw [eq'] at path
  simp at path

  have get (i : Nat) (_ : Array.size nfa.nodes ≤ i) (h₂ : i < nfa₂.val.nodes.size) :
    nfa₂.val[i] = nfa₁.val[i]'(Nat.lt_trans h₂ nfa₁.property) := by
    rw [pushRegex_get_lt eq₁.symm]

  obtain ⟨i, s₂, path, step₂⟩ := path
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
  obtain ⟨s₁, path₁, path₂⟩ := pathIn_split eq₁.symm nfa₂.property lti
    (ge_pushRegex_start eq₁.symm) path
  obtain ⟨p₁, eqs₁, m₁⟩ := ih₁ eq₁.symm path₁
  have path₂ : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start.val s₁ s' := by
    have step₂ : stepIn nfa₂ nfa.nodes.size i s₂ next s' := by
      apply step₂.cast lti
      rw [get i step₂.h₁ lti]
    refine ⟨_, _, ?_, step₂⟩
    apply path₂.cast' nfa₂.val.start.isLt (Nat.le_of_lt nfa₁.property) get
  obtain ⟨p₂, eqs₂, m₂⟩ := ih₂ eq₂.symm path₂

  exact ⟨p₁ ++ p₂, by simp [eqs₁, eqs₂], .concat _ _ _ _ _ rfl m₁ m₂⟩

theorem matches_prefix_of_path.star (eq : pushRegex nfa next (.star r) = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val s s')
  (ih : ∀ {nfa next result s s'},
    pushRegex nfa next r = result →
    pathToNext result next nfa.nodes.size result.val.start.val s s' →
    ∃ p, s = p ++ s' ∧ Regex.matches { data := p } r) :
  ∃ p, s = p ++ s' ∧ (Regex.star r).matches ⟨p⟩ := by
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq'

  obtain ⟨i, s'', path, step⟩ := path
  have eqis := eq_of_step_next eq step
  simp [eqis] at path
  have loop : starLoop eq s s' := by
    apply starLoop.intro eq
    suffices result.val.start = nfa.nodes.size by
      rw [this] at path
      exact path
    rw [eq']
    simp
    rw [eq₄]
  apply matches_prefix_of_starLoop eq ?_ loop

  intro cs cs' rStart mem path'
  apply ih eq₂.symm
  simp [eq₁]

  simp [eq', eq₄, get_eq_nodes_get, eq₃] at mem
  rw [Array.get_set_eq] at mem
  simp [NFA.Node.εStep] at mem
  cases mem with
  | inl eqr =>
    rw [eqr] at path'
    apply path'.cast

    intro j h₁ h₂
    simp [eq', eq₄, eq₃] at h₂
    exists h₂

    simp [eq', get_eq_nodes_get, eq₄]
    simp [eq₃]
    rw [Array.get_set_ne]
    simp
    exact Nat.ne_of_lt h₁
  | inr eqr =>
    exfalso
    have : nfa.nodes.size + 1 ≤ next := eqr ▸ le_of_pathToNext path'
    exact Nat.lt_irrefl _ (Nat.lt_trans this next.isLt)
where
  eq_of_step_next {i cs cs'} (eq : pushRegex nfa next (.star r) = result)
    (step : stepIn result nfa.nodes.size i cs next cs') :
    i = nfa.nodes.size ∧ cs = cs' := by
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      eq₁ eq₂ eq₃ eq₄ eq'

    cases Nat.lt_or_ge i (nfa.nodes.size + 1) with
    | inl lt =>
      obtain ⟨_, _, node⟩ := rStart_of_push_star eq
      have eqi := Nat.eq_of_ge_of_lt step.h₁ lt
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

theorem matches_prefix_of_path (eq : pushRegex nfa next r = result)
  (path : pathToNext result next nfa.nodes.size result.val.start.val s s') :
  ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
  induction r generalizing nfa next s s' with
  | empty =>
    apply pushRegex.empty eq
    intro eq
    rw [eq] at path
    obtain ⟨i, _, path, step⟩ := path
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
    obtain ⟨i, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
    cases path with
    | base _ _ eqs => exact ⟨[], eqs, .epsilon rfl⟩
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
    obtain ⟨i, _, path, step⟩ := path
    have : i < nfa.nodes.size + 1 := by
      have := step.h₂
      simp at this
      exact this
    have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt (le_of_pathIn_right path) this
    cases step <;> simp [this, NFA.Node.charStep, NFA.Node.εStep] at *
    cases path with
    | base _ _ eqs => exact ⟨[c], by simp [*], .char c rfl⟩
    | step step rest =>
      cases step with
      | charStep _ _ step =>
        simp [NFA.Node.charStep] at step
        have := le_of_pathIn_left rest
        exact absurd next.isLt (Nat.not_lt_of_ge (step.right ▸ this))
      | εStep _ _ step => simp [NFA.Node.εStep] at step
  | group i r ih => exact matches_prefix_of_path.group eq path ih
  | alternate r₁ r₂ ih₁ ih₂ => exact matches_prefix_of_path.alternate eq path ih₁ ih₂
  | concat r₁ r₂ ih₁ ih₂ => exact matches_prefix_of_path.concat eq path ih₁ ih₂
  | star r ih => exact matches_prefix_of_path.star eq path ih

theorem matches_prefix_of_compile_path (eq : NFA.compile r = nfa)
  (path : pathToNext nfa 0 1 nfa.start.val s s') :
  ∃ p, s = p ++ s' ∧ r.matches ⟨p⟩ := by
  set result := NFA.done.pushRegex ⟨0, by decide⟩ r
  have : nfa = result.val := by
    rw [←eq]
    rfl
  rw [this] at path
  exact matches_prefix_of_path rfl path

end NFA
