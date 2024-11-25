-- When the compiled NFA accepts a string, the regex matches it.
import RegexCorrectness.Semantics.Expr.Matches
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Transition.Path.Basic

open Regex.Data (Expr)

namespace Regex.NFA

theorem rStart_of_push_star (eq : pushRegex nfa next (.star r) = result) :
  ∃ rStart, nfa.nodes.size + 1 ≤ rStart ∧ result.val[nfa.nodes.size]'result.property = .split rStart next := by
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' property
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

theorem eq_next_of_pathIn (eq : pushRegex nfa next r = result)
  (assm : next' < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size i next' cs) :
  next' = next := by
  induction path with
  | last step =>
    have := eq_or_ge_of_step_pushRegex eq step.h₁ step.h₂ step.step
    cases this with
    | inl eq => exact eq
    | inr ge => exact absurd assm (Nat.not_lt_of_le ge)
  | more _ _ ih => exact ih assm

theorem pathIn.split (eq : pushRegex nfa next r = result)
  (assm₁ : j < nfa.nodes.size) (assm₂ : nfa.nodes.size ≤ i)
  (path : pathIn result lb i j cs) :
  j = next ∨
  ∃ cs₁ cs₂,
    cs = cs₁ ++ cs₂ ∧
    pathIn result nfa.nodes.size i next cs₁ ∧
    pathIn result lb next j cs₂ := by
  induction path with
  | @last i j cs step =>
    have := eq_or_ge_of_step_pushRegex eq assm₂ step.h₂ step.step
    cases this with
    | inl eq => exact .inl eq
    | inr ge => exact absurd assm₁ (Nat.not_lt_of_le ge)
  | @more i j k cs₁ cs₂ step rest ih =>
    have := eq_or_ge_of_step_pushRegex eq assm₂ step.h₂ step.step
    cases this with
    | inl eq =>
      subst eq
      exact .inr ⟨cs₁, cs₂, rfl, .last (step.castBound' assm₂), rest⟩
    | inr ge =>
      have ih := ih assm₁ ge
      cases ih with
      | inl eq => exact .inl eq
      | inr ih =>
        have ⟨cs₃, cs₄, eqs, path₁, path₂⟩ := ih
        exact .inr ⟨cs₁ ++ cs₃, cs₄, by simp [eqs], .more (step.castBound' assm₂) path₁, path₂⟩

inductive starLoop (eq : pushRegex nfa next (.star r) = result) : List Char → Prop where
  | last (step : stepIn result nfa.nodes.size nfa.nodes.size next cs) : starLoop eq cs
  | loop
    (path : pathIn result (nfa.nodes.size + 1) (rStart_of eq) nfa.nodes.size cs₁)
    (rest : starLoop eq cs₂) : starLoop eq (cs₁ ++ cs₂)

theorem starLoop.intro' (eq : pushRegex nfa next (.star r) = result)
  (assm₁ : i < result.val.nodes.size) (assm₂ : nfa.WellFormed) (assm₃ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size i next cs) :
  if i = nfa.nodes.size then
    (stepIn result nfa.nodes.size nfa.nodes.size next cs) ∨
    (∃ cs₁ cs₂,
      cs = cs₁ ++ cs₂ ∧
      pathIn result (nfa.nodes.size + 1) (rStart_of eq) nfa.nodes.size cs₁ ∧
      starLoop eq cs₂)
  else
    ∃ cs₁ cs₂,
      cs = cs₁ ++ cs₂ ∧
      pathIn result (nfa.nodes.size + 1) i nfa.nodes.size cs₁ ∧
      starLoop eq cs₂ := by
  induction path with
  | @last i j cs step =>
    cases Nat.eq_or_lt_of_le step.h₁ with
    | inl eqi =>
      simp [eqi]
      exact .inl (eqi ▸ step)
    | inr gt =>
      apply pushRegex.star eq
      intro placeholder compiled patched nfa' property
        eq₁ eq₂ eq₃ eq₄ eq
      have : stepIn compiled nfa.nodes.size i j cs := by
        have lt : i < compiled.val.nodes.size := by
          simp [eq, eq₄, eq₃] at assm₁
          exact assm₁
        apply step.cast lt
        simp [eq, eq₄, NFA.get_eq_nodes_get, eq₃]
        rw [Array.get_set_ne (hj := lt) (h := by simp; exact Nat.ne_of_lt gt)]
      have := eq_or_ge_of_step_pushRegex eq₂.symm (by simp [eq₁]; exact gt) this.h₂ this.step
      cases this with
      | inl eq => exact absurd eq (Nat.ne_of_lt assm₃)
      | inr ge =>
        simp [eq₁] at ge
        exact (Nat.lt_irrefl _ (Nat.lt_trans ge assm₃)).elim
  | @more i j k cs₁ cs₂ step rest ih =>
    split
    next h =>
      have := rStart_of_spec eq
      cases step with
      | charStep _ _ step => simp [h, this, Node.charStep] at step
      | εStep _ _ step =>
        simp [h, this, Node.εStep] at step
        have eqj : j = rStart_of eq := by
          cases step with
          | inl eq => exact eq
          | inr eq => exact absurd assm₃ (Nat.not_lt_of_le (eq ▸ rest.le_left))
        have : j ≠ nfa.nodes.size := Nat.ne_of_gt (eqj ▸ this.left)
        have ih := ih eq rest.lt_left assm₃
        simp [this] at ih
        have ⟨cs₃, cs₄, eqs, path', loop'⟩ := ih
        exact .inr ⟨cs₃, cs₄, by simp [eqs], eqj ▸ path', loop'⟩
    next h =>
      have gt : nfa.nodes.size < i := Nat.lt_of_le_of_ne step.h₁ (Ne.symm h)
      have ih := ih eq (step.lt_right (pushRegex_wf eq assm₂ assm₃)) assm₃
      split at ih
      next h' =>
        cases ih with
        | inl step' =>
          have path := pathIn.last (step.castBound' gt)
          exact ⟨cs₁, cs₂, rfl, h' ▸ path, .last step'⟩
        | inr ih =>
          have ⟨cs₃, cs₄, eqs, path', loop'⟩ := ih
          have path'' : pathIn result (nfa.nodes.size + 1) i j cs₁ := .last (step.castBound' gt)
          have loop'' : starLoop eq (cs₃ ++ cs₄) := .loop path' loop'
          exact ⟨cs₁, cs₃ ++ cs₄, by simp [eqs], h' ▸ path'', loop''⟩
      next h' =>
        have ⟨cs₃, cs₄, eqs, path', loop'⟩ := ih
        exact ⟨cs₁ ++ cs₃, cs₄, by simp [eqs], .more (step.castBound' gt) path', loop'⟩

theorem starLoop.intro (eq : pushRegex nfa next (.star r) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size nfa.nodes.size next cs) :
  starLoop eq cs := by
  have loop := starLoop.intro' eq result.property assm₁ assm₂ path
  simp at loop
  match loop with
  | .inl step => exact .last step
  | .inr ⟨cs₁, cs₂, eqs, path, loop⟩ => exact eqs ▸ .loop path loop

theorem matches_of_starLoop (eq : pushRegex nfa next (.star r) = result)
  (mr : ∀ {cs},
    pathIn result (nfa.nodes.size + 1) (rStart_of eq) nfa.nodes.size cs →
    r.matches cs)
  (loop : starLoop eq cs) :
  (Expr.star r).matches cs := by
  induction loop with
  | last step =>
    have := rStart_of_spec eq
    cases step with
    | charStep _ _ step => simp [this, Node.charStep] at step
    | εStep _ _ step => exact .starEpsilon
  | loop path _ m₂ => exact .starConcat _ _ _ (mr path) m₂

theorem matches_of_pathIn.group (eq : pushRegex nfa next (.group i r) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih : ∀ {nfa next result cs},
    pushRegex nfa next r = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    r.matches cs) :
  (Expr.group i r).matches cs := by
  have wf_result := pushRegex_wf eq assm₁ assm₂

  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property eq₁ eq₂ eq₃ eq

  simp [eq] at path
  simp [eq] at wf_result
  have wf' := pushNode_wf eq₁ assm₁ (by simp [Node.inBounds]; omega)
  have wf'' := pushRegex_wf eq₂.symm wf' wf'.start_lt

  suffices pathIn nfa'' nfa'.val.nodes.size nfa''.val.start nfa'.val.start cs from
    .group (ih eq₂.symm wf' wf'.start_lt this)

  have : nfa'.val.start < nfa''.val.nodes.size := by
    simp [eq₁]
    exact Nat.lt_trans nfa'.property nfa''.property

  have eqStart : nfa'''.val[nfa'''.val.start]'wf_result.start_lt = .save (2 * i) nfa''.val.start := by
    have : nfa'''.val.start = nfa''.val.nodes.size := by
      rw [eq₃]
      simp
    simp [this, eq₃]

  have eqStart' : nfa''.val[nfa'.val.start] = .save (2 * i + 1) next := by
    rw [pushRegex_get_lt eq₂.symm nfa'.val.start wf'.start_lt]
    have : nfa'.val.start = nfa.nodes.size := by
      rw [eq₁]
      simp
    simp [this, eq₁]

  cases path with
  | last step =>
    have step := step.step
    simp [eqStart, Node.charStep, Node.εStep] at step
    have : next < nfa''.val.start :=
      calc
        _ < nfa.nodes.size := assm₂
        _ < nfa'.val.nodes.size := nfa'.property
        _ ≤ nfa''.val.start := ge_pushRegex_start eq₂.symm
    rw [step] at this
    exact (Nat.lt_irrefl _ this).elim
  | @more i j k cs₁ cs₂ step rest =>
    cases step with
    | charStep _ _ step => simp [eqStart, Node.charStep] at step
    | εStep _ _ step =>
      simp [eqStart, Node.εStep] at step
      subst step
      simp
      have rest : pathIn nfa'' nfa.nodes.size nfa''.val.start next cs₂ := by
        apply rest.cast' wf''.start_lt (Nat.le_of_lt nfa'''.property) wf''
        intro i _ h₂
        rw [eq₃, pushNode_get_lt _ h₂]
      have := rest.split eq₂.symm (Nat.lt_trans assm₂ nfa'.property) (ge_pushRegex_start eq₂.symm)
      cases this with
      | inl eq =>
        rw [eq₁] at eq
        simp at eq
        exact (Nat.lt_irrefl _ (eq ▸ assm₂)).elim
      | inr split =>
        have ⟨cs₃, cs₄, eqs, path₁, path₂⟩ := split
        cases path₂ with
        | last step =>
          cases step with
          | charStep _ _ step => simp [eqStart', Node.charStep] at step
          | εStep =>
            simp at eqs
            exact eqs ▸ path₁
        | more step rest₂ =>
          cases step with
          | charStep _ _ step => simp [eqStart', Node.charStep] at step
          | εStep _ _ step =>
            simp [eqStart', Node.εStep] at step
            have : nfa.nodes.size ≤ next := step ▸ rest₂.le_left
            exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt this assm₂)).elim

theorem matches_of_pathIn.alternate (eq : pushRegex nfa next (.alternate r₁ r₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih₁ : ∀ {nfa next result cs},
    pushRegex nfa next r₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    r₁.matches cs)
  (ih₂ : ∀ {nfa next result cs},
    pushRegex nfa next r₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    r₂.matches cs) :
  (Expr.alternate r₁ r₂).matches cs := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ final property eq₁ eq₂ eq₃ eq₄ eq₅ eq'

  simp [eq'] at path

  have wf_nfa₁ : nfa₁.val.WellFormed :=
    pushRegex_wf eq₁.symm assm₁ assm₂
  have wf_nfa₂ : nfa₂.val.WellFormed :=
    pushRegex_wf eq₃.symm wf_nfa₁ (Nat.lt_trans assm₂ nfa₁.property)
  have wf_final : final.val.WellFormed := by
    have := pushRegex_wf eq assm₁ assm₂
    simp [eq'] at this
    exact this

  have startNode : final.val[final.val.start]'wf_final.start_lt = .split start₁ start₂ := by
    simp [eq₅]
  have neStart₁ : next ≠ start₁ := by
    apply Nat.ne_of_lt
    apply Nat.lt_of_lt_of_le assm₂
    exact eq₂ ▸ ge_pushRegex_start eq₁.symm
  have neStart₂ : next ≠ start₂ := by
    apply Nat.ne_of_lt
    apply Nat.lt_of_lt_of_le (Nat.lt_trans assm₂ nfa₁.property)
    exact eq₄ ▸ ge_pushRegex_start eq₃.symm

  have get₂ (i : Nat) (_ : nfa.nodes.size ≤ i) (h₂: i < nfa₂.val.nodes.size) :
    nfa₂.val[i] = final.val[i]'(Nat.lt_trans h₂ final.property) := by
    simp [eq₅]
    rw [pushNode_get_lt]

  have get₁ (i : Nat) (h₁ : nfa.nodes.size ≤ i) (h₂: i < nfa₁.val.nodes.size) :
    nfa₁.val[i] = final.val[i]'(Nat.lt_trans (Nat.lt_trans h₂ nfa₂.property) final.property) := by
    rw [←get₂ i h₁ (Nat.lt_trans h₂ nfa₂.property)]
    rw [pushRegex_get_lt eq₃.symm]

  cases path with
  | last step =>
    have step := step.step
    simp [startNode, Node.charStep, Node.εStep] at step
    have := step.imp neStart₁ neStart₂
    simp at this
  | @more _ j _ _ cs step rest =>
    cases step with
    | charStep _ _ step => simp [startNode, Node.charStep] at step
    | εStep _ _ step =>
      simp [startNode, Node.εStep] at step
      simp
      cases step with
      | inl eqStart₁ =>
        simp [eqStart₁, eq₂] at rest
        have : pathIn nfa₁ nfa.nodes.size nfa₁.val.start next cs :=
          rest.cast' wf_nfa₁.start_lt (Nat.le_of_lt (Nat.lt_trans nfa₂.property final.property)) wf_nfa₁ get₁
        exact .alternateLeft (ih₁ eq₁.symm assm₁ assm₂ this)
      | inr eqStart₂ =>
        simp [eqStart₂, eq₄] at rest
        have : pathIn nfa₂ nfa.nodes.size nfa₂.val.start next cs :=
          rest.cast' wf_nfa₂.start_lt (Nat.le_of_lt final.property) wf_nfa₂ get₂
        have : pathIn nfa₂ nfa₁.val.nodes.size nfa₂.val.start next cs := by
          apply this.castLE
          . exact ge_pushRegex_start eq₃.symm
          . intro i j h₁ h₂ step h₃
            have := eq_or_ge_of_step_pushRegex eq₃.symm h₁ h₂ step
            cases this with
            | inl eq =>
              simp [eq] at h₃
              exact (Nat.lt_irrefl _ (Nat.lt_of_le_of_lt h₃ assm₂)).elim
            | inr ge => exact ge
        exact .alternateRight (ih₂ eq₃.symm wf_nfa₁ (Nat.lt_trans assm₂ nfa₁.property) this)

theorem matches_of_pathIn.concat (eq : pushRegex nfa next (.concat r₁ r₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih₁ : ∀ {nfa next result cs},
    pushRegex nfa next r₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    r₁.matches cs)
  (ih₂ : ∀ {nfa next result cs},
    pushRegex nfa next r₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    r₂.matches cs) :
  (Expr.concat r₁ r₂).matches cs := by
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq'

  rw [eq'] at path
  simp at path

  have wf_nfa₂ : nfa₂.val.WellFormed :=
    pushRegex_wf eq₂.symm assm₁ assm₂

  have get (i : Nat) (_ : Array.size nfa.nodes ≤ i) (h₂ : i < nfa₂.val.nodes.size) :
    nfa₂.val[i] = nfa₁.val[i]'(Nat.lt_trans h₂ nfa₁.property) := by
    rw [pushRegex_get_lt eq₁.symm]

  have := path.split eq₁.symm (Nat.lt_trans assm₂ nfa₂.property) (ge_pushRegex_start eq₁.symm)
  cases this with
  | inl eq =>
    have : next < nfa₂.val.start :=
      calc next
        _ < nfa.nodes.size := assm₂
        _ ≤ nfa₂.val.start := ge_pushRegex_start eq₂.symm
    exact (Nat.lt_irrefl _ (eq ▸ this)).elim
  | inr split =>
    have ⟨cs₁, cs₂, eqs, path₁, path₂⟩ := split
    have m₁ := ih₁ eq₁.symm wf_nfa₂ wf_nfa₂.start_lt path₁
    have path₂ : pathIn nfa₂ nfa.nodes.size nfa₂.val.start next cs₂ :=
      path₂.cast' wf_nfa₂.start_lt (Nat.le_of_lt nfa₁.property) wf_nfa₂ get
    have m₂ := ih₂ eq₂.symm assm₁ assm₂ path₂
    exact eqs ▸ .concat _ _ _ _ m₁ m₂

theorem matches_of_pathIn.star (eq : pushRegex nfa next (.star r) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih : ∀ {nfa next result cs},
    pushRegex nfa next r = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    Expr.matches cs r) :
  (Expr.star r).matches cs := by
  have : result.val.start = nfa.nodes.size := by
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' property
      _ _ _ eq₄ eq'
    simp [eq', eq₄]
  have : starLoop eq cs := by
    apply starLoop.intro eq assm₁ assm₂
    rw [this] at path
    exact path
  apply matches_of_starLoop eq ?_ this
  intro cs path

  apply pushRegex.star eq
  intro placeholder compiled patched nfa' property
    eq₁ eq₂ eq₃ eq₄ eq'

  have wf_placeholder : placeholder.val.WellFormed :=
    pushNode_wf eq₁ assm₁ (by simp [Node.inBounds])
  have wf_compiled : compiled.val.WellFormed :=
    pushRegex_wf eq₂.symm wf_placeholder placeholder.property

  suffices path : pathIn compiled (nfa.nodes.size + 1) compiled.val.start nfa.nodes.size cs by
    have : placeholder.val.nodes.size = nfa.nodes.size + 1 := by
      simp [eq₁]
    rw [←this] at path
    exact ih eq₂.symm wf_placeholder placeholder.property path

  have : rStart_of eq = compiled.val.start := by
    have ⟨_, eq⟩ := rStart_of_spec eq
    have : result.val[nfa.nodes.size] = .split compiled.val.start next := by
      simp [eq', NFA.get_eq_nodes_get, eq₄, eq₃]
    rw [this] at eq
    simp at eq
    exact eq.symm
  rw [this] at path

  apply path.cast' wf_compiled.start_lt ?_ wf_compiled ?_
  . simp [eq', eq₄, eq₃]
  . intro i h₁ h₂
    simp [eq', eq₄, NFA.get_eq_nodes_get, eq₃]
    rw [Array.get_set_ne (hj := h₂) (h := (by simp; exact Nat.ne_of_lt h₁))]

theorem matches_of_pathIn_pushRegex
  (eq : pushRegex nfa next r = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs) :
  r.matches cs := by
  induction r generalizing nfa next cs with
  | empty =>
    have wf := pushRegex_wf eq assm₁ assm₂
    have get : result.val[result.val.start]'wf.start_lt = .fail := by
      apply pushRegex.empty eq
      intro eq
      simp [eq]
    cases path with
    | last step => cases step <;> simp [get, Node.charStep, Node.εStep] at *
    | more step => cases step <;> simp [get, Node.charStep, Node.εStep] at *
  | epsilon =>
    have wf := pushRegex_wf eq assm₁ assm₂
    have get : result.val[result.val.start]'wf.start_lt = .epsilon next := by
      apply pushRegex.epsilon eq
      intro eq
      simp [eq]
    cases path with
    | last step =>
      cases step with
      | charStep _ _ step => simp [get, Node.charStep] at step
      | εStep _ _ step => exact .epsilon
    | more step rest =>
      have step := step.step
      simp [get, Node.charStep, Node.εStep] at step
      rw [step] at rest
      exact (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le assm₂ rest.le_left)).elim
  | char c =>
    have wf := pushRegex_wf eq assm₁ assm₂
    have get : result.val[result.val.start]'wf.start_lt = .char c next := by
      apply pushRegex.char eq
      intro eq
      simp [eq]
    cases path with
    | last step =>
      cases step with
      | charStep _ _ step =>
        simp [get, Node.charStep] at step
        rw [step]
        exact .char _
      | εStep _ _ step => simp [get, Node.εStep] at step
    | more step rest =>
      have step := step.step
      simp [get, Node.charStep, Node.εStep] at step
      rw [step] at rest
      exact (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le assm₂ rest.le_left)).elim
  | classes cls =>
    have wf := pushRegex_wf eq assm₁ assm₂
    have get : result.val[result.val.start]'wf.start_lt = .sparse cls next := by
      apply pushRegex.sparse eq
      intro eq
      simp [eq]
    cases path with
    | last step =>
      cases step with
      | charStep _ _ step =>
        simp [get, Node.charStep] at step
        exact .sparse cls _ step
      | εStep _ _ step => simp [get, Node.εStep] at step
    | more step rest =>
      have step := step.step
      simp [get, Node.charStep, Node.εStep] at step
      rw [step.right] at rest
      exact (Nat.lt_irrefl _ (Nat.lt_of_lt_of_le assm₂ rest.le_left)).elim
  | group i r ih => exact matches_of_pathIn.group eq assm₁ assm₂ path ih
  | alternate r₁ r₂ ih₁ ih₂ => exact matches_of_pathIn.alternate eq assm₁ assm₂ path ih₁ ih₂
  | concat r₁ r₂ ih₁ ih₂ => exact matches_of_pathIn.concat eq assm₁ assm₂ path ih₁ ih₂
  | star r ih => exact matches_of_pathIn.star eq assm₁ assm₂ path ih

theorem matches_of_pathIn_compile (eq : compile r = nfa)
  (path : pathIn nfa 1 nfa.start 0 cs) :
  r.matches cs := by
  set result := NFA.done.pushRegex 0 r
  have : nfa = result.val := by
    rw [←eq]
    rfl
  rw [this] at path
  exact matches_of_pathIn_pushRegex rfl done_WellFormed (by simp [done]) path

end Regex.NFA
