-- When the compiled NFA accepts a string, the regex matches it.
import RegexCorrectness.Semantics.Expr.Matches
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Transition.Path.Basic

open Regex.Data (Expr)

namespace Regex.NFA

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

section

set_option autoImplicit false
open Compile.ProofData

inductive StarLoop [Star] : List _root_.Char → Prop where
  | last {cs} (step : nfa'.stepIn nfa.nodes.size nfa.nodes.size next cs) : StarLoop cs
  | loop {cs₁ cs₂}
    (path : nfa'.pathIn (nfa.nodes.size + 1) Star.nfaExpr.start nfa.nodes.size cs₁)
    (rest : StarLoop cs₂) : StarLoop (cs₁ ++ cs₂)

theorem StarLoop.intro' [pd : Star] {i j cs}
  (assm₁ : i < nfa'.nodes.size) (assm₂ : nfa.WellFormed) (assm₃ : next < nfa.nodes.size) (assm₄ : j = next)
  (path : nfa'.pathIn nfa.nodes.size i j cs) :
  if i = nfa.nodes.size then
    (nfa'.stepIn nfa.nodes.size nfa.nodes.size next cs) ∨
    (∃ cs₁ cs₂,
      cs = cs₁ ++ cs₂ ∧
      nfa'.pathIn (nfa.nodes.size + 1) Star.nfaExpr.start nfa.nodes.size cs₁ ∧
      StarLoop cs₂)
  else
    ∃ cs₁ cs₂,
      cs = cs₁ ++ cs₂ ∧
      nfa'.pathIn (nfa.nodes.size + 1) i nfa.nodes.size cs₁ ∧
      StarLoop cs₂ := by
  induction path with
  | @last i j cs step =>
    match Star.of_stepIn step with
    | .inl ⟨eqi, _, eqcs⟩ =>
      subst eqi eqcs
      simp
      exact .inl (assm₄ ▸ step)
    | .inr ⟨lt, step'⟩ =>
      have := Nat.ne_of_gt lt
      simp [this]
      have : Star.nfaPlaceholder.nodes.size ≤ i := by
        simp [Star.nfaPlaceholder]
        exact lt
      have := eq_or_ge_of_step_pushRegex rfl this (pd.size_eq_expr' ▸ assm₁) step'.step
      subst assm₄
      cases this with
      | inl eq => exact absurd (eq ▸ assm₃) (Nat.lt_irrefl _)
      | inr le =>
        simp [Star.nfaPlaceholder] at le
        exact absurd (Nat.lt_trans assm₃ le) (Nat.lt_irrefl _)
  | @more i j k cs₁ cs₂ step rest ih =>
    match Star.of_stepIn step with
    | .inl ⟨eqi, eqj, eqcs⟩ =>
      subst eqi eqcs
      simp
      cases eqj with
      | inl eqj =>
        subst eqj
        have ih := ih (pd.size_eq_expr' ▸ (pd.wf_expr assm₂).start_lt) assm₄
        have : Star.nfaExpr.start ≠ nfa.nodes.size := by
          apply Nat.ne_of_gt
          have := ge_pushRegex_start (result := ⟨Star.nfaExpr, _⟩) rfl
          simp [Star.nfaPlaceholder] at this
          exact this
        simp [this] at ih
        exact .inr ih
      | inr eqj =>
        simp [eqj] at rest
        have h₁ := rest.le_left
        exact absurd (Nat.lt_of_lt_of_le assm₃ h₁) (Nat.lt_irrefl _)
    | .inr ⟨lt, step'⟩ =>
      have : i ≠ nfa.nodes.size := Nat.ne_of_gt lt
      simp [this]
      have ih := ih (pd.size_eq_expr' ▸ (step'.lt_right (pd.wf_expr assm₂))) assm₄
      split at ih
      next eqj =>
        match ih with
        | .inl step'' =>
          have : nfa'.stepIn (nfa.nodes.size + 1) i j cs₁ := step.castBound' lt
          exact ⟨cs₁, cs₂, rfl, .last (eqj ▸ this), StarLoop.last step''⟩
        | .inr ⟨cs₃, cs₄, eqs', path', loop'⟩ =>
          have : nfa'.stepIn (nfa.nodes.size + 1) i j cs₁ := step.castBound' lt
          exact ⟨cs₁, cs₃ ++ cs₄, by simp [eqs'], .last (eqj ▸ this), .loop path' loop'⟩
      next nej =>
        have ⟨cs₃, cs₄, eqs', path', loop'⟩ := ih
        have : nfa'.pathIn (nfa.nodes.size + 1) i nfa.nodes.size (cs₁ ++ cs₃) :=
          .more (step.castBound' lt) path'
        exact ⟨cs₁ ++ cs₃, cs₄, by simp [eqs'], this, loop'⟩

theorem StarLoop.intro [Star] {cs}
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : nfa'.pathIn nfa.nodes.size nfa.nodes.size next cs) :
  StarLoop cs := by
  have loop := StarLoop.intro' size_lt assm₁ assm₂ rfl path
  simp at loop
  match loop with
  | .inl step => exact .last step
  | .inr ⟨cs₁, cs₂, eqs, path, loop⟩ => exact eqs ▸ .loop path loop

theorem matches_of_StarLoop [pd : Star] {e cs}
  (mr : ∀ {cs},
    nfa'.pathIn (nfa.nodes.size + 1) Star.nfaExpr.start nfa.nodes.size cs →
    e.matches cs)
  (loop : StarLoop cs) :
  (Expr.star e).matches cs := by
  induction loop with
  | last step =>
    cases step with
    | charStep _ _ step => simp [pd.get_start, Node.charStep] at step
    | εStep _ _ step => exact .starEpsilon
  | loop path _ m₂ => exact .starConcat _ _ _ (mr path) m₂

end

theorem matches_of_pathIn.group (eq : pushRegex nfa next (.group i e) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih : ∀ {nfa next result cs},
    pushRegex nfa next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    e.matches cs) :
  (Expr.group i e).matches cs := by
  open Compile.ProofData Group in
  let pd := Group.intro eq
  simp [pd.eq_result eq] at path

  have wf_close := pd.wf_close assm₁ assm₂
  have wf_expr := pd.wf_expr assm₁ assm₂

  suffices nfaExpr.pathIn nfaClose.nodes.size nfaExpr.start nfaClose.start cs from
    .group (ih rfl wf_close wf_close.start_lt this)

  cases path with
  | last step =>
    have ⟨eq, _⟩ := stepIn_open_iff.mp step
    have ge : nfa.nodes.size ≤ nfaExpr.start :=
      calc
        _ ≤ nfaClose.nodes.size := Nat.le_of_lt nfaClose_property
        _ ≤ _ := ge_pushRegex_start rfl
    exact absurd (eq ▸ assm₂) (Nat.not_lt_of_ge ge)
  | @more i j k cs₁ cs₂ step rest =>
    have ⟨eqj, eqcs₁⟩ := stepIn_open_iff.mp step
    subst eqj eqcs₁

    have path : nfaExpr.pathIn nfa.nodes.size nfaExpr.start next cs₂ := by
      apply rest.cast' wf_expr.start_lt (Nat.le_of_lt pd.size_lt_expr') wf_expr
      intro i _ h₂
      exact (pd.get_lt_expr h₂).symm
    have := path.split rfl (Nat.lt_trans assm₂ nfaClose_property) (ge_pushRegex_start rfl)
    match this with
    | .inl eq =>
      have ge : nfa.nodes.size ≤ nfaClose.start := Nat.le_refl _
      exact absurd (eq ▸ assm₂) (Nat.not_lt_of_ge ge)
    | .inr ⟨cs₃, cs₄, eqs, path', path''⟩ =>
      have get : nfaExpr[nfaClose.start]'size_lt_nfa_expr = .save (2 * tag + 1) next := by
        simp [nfaClose]
        exact get_close_expr
      cases path'' with
      | last step' =>
        have step' : nfaExpr.stepIn nfa.nodes.size nfaClose.start next cs₄ := step'
        cases step' with
        | charStep _ _ step'' => simp [get, Node.charStep] at step''
        | εStep _ _ step'' =>
          simp at eqs
          simp [eqs]
          exact path'
      | @more l m n cs₅ cs₆ step' rest' =>
        have step' : nfaExpr.stepIn nfa.nodes.size nfaClose.start m cs₅ := step'
        cases step' with
        | charStep _ _ step'' => simp [get, Node.charStep] at step''
        | εStep _ _ step'' =>
          simp [get, Node.εStep] at step''
          exact absurd assm₂ (Nat.not_lt_of_le (step'' ▸ rest'.le_left))

theorem matches_of_pathIn.alternate (eq : pushRegex nfa next (.alternate e₁ e₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih₁ : ∀ {nfa next result cs},
    pushRegex nfa next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    e₁.matches cs)
  (ih₂ : ∀ {nfa next result cs},
    pushRegex nfa next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    e₂.matches cs) :
  (Expr.alternate e₁ e₂).matches cs := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [pd.eq_result eq] at path
  cases path with
  | last step =>
    have ⟨eq, _⟩ := stepIn_start_iff.mp step
    cases eq with
    | inl eq =>
      have : nfa.nodes.size ≤ nfa₁.start := ge_pushRegex_start rfl
      exact absurd (eq ▸ assm₂) (Nat.not_lt_of_le this)
    | inr eq =>
      have : nfa.nodes.size < nfa₂.start :=
        calc
          _ < nfa₁.nodes.size := nfa₁_property
          _ ≤ nfa₂.start := ge_pushRegex_start rfl
      exact absurd (eq ▸ assm₂) (Nat.not_lt_of_lt this)
  | @more i j k cs₁ cs₂ step rest =>
    have ⟨eqj, eqcs₁⟩ := stepIn_start_iff.mp step
    subst eqcs₁
    simp

    have wf₁ := wf₁ assm₁ assm₂
    have wf₂ := wf₂ assm₁ assm₂

    cases eqj with
    | inl eqj₁ =>
      subst eqj₁
      refine .alternateLeft (ih₁ rfl assm₁ assm₂ ?_)
      show nfa₁.pathIn nfa.nodes.size nfa₁.start next cs₂
      apply rest.cast' wf₁.start_lt (Nat.le_of_lt size_lt₁) wf₁
      intro i _ h₂
      simp [get_lt₁ h₂]
    | inr eqj₂ =>
      subst eqj₂
      refine .alternateRight (ih₂ rfl wf₁ (Nat.lt_trans assm₂ nfa₁_property) ?_)
      show nfa₂.pathIn nfa₁.nodes.size nfa₂.start next cs₂
      have path : nfa₂.pathIn nfa.nodes.size nfa₂.start next cs₂ := by
        apply rest.cast' wf₂.start_lt (Nat.le_of_lt size_lt₂) wf₂
        intro i _ h₂
        simp [get_lt₂ h₂]
      apply path.castLE (ge_pushRegex_start rfl)
      intro i j h₁ h₂ step le
      have := eq_or_ge_of_step_pushRegex rfl h₁ h₂ step
      cases this with
      | inl eq => exact absurd (eq ▸ assm₂) (Nat.not_lt_of_ge le)
      | inr ge => exact ge

theorem matches_of_pathIn.concat (eq : pushRegex nfa next (.concat e₁ e₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih₁ : ∀ {nfa next result cs},
    pushRegex nfa next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    e₁.matches cs)
  (ih₂ : ∀ {nfa next result cs},
    pushRegex nfa next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    e₂.matches cs) :
  (Expr.concat e₁ e₂).matches cs := by
  open Compile.ProofData Concat in
  let pd := Concat.intro eq
  simp [pd.eq_result eq] at path

  have wf₂ := wf₂ assm₁ assm₂

  have := path.split rfl (Nat.lt_trans assm₂ nfa₂_property) (ge_pushRegex_start rfl)
  match this with
  | .inl eq => exact absurd (eq ▸ assm₂) (Nat.not_lt_of_ge (ge_pushRegex_start rfl))
  | .inr ⟨cs₁, cs₂, eqs, path₁, path₂⟩ =>
    have m₁ := ih₁ rfl wf₂ wf₂.start_lt path₁
    have path₂ : nfa'.pathIn nfa.nodes.size nfa₂.start next cs₂ := path₂
    have path₂ : nfa₂.pathIn nfa.nodes.size nfa₂.start next cs₂ := by
      apply path₂.cast' wf₂.start_lt (Nat.le_of_lt size₂_lt) wf₂
      intro i _ h₂
      simp [get_lt₂ h₂]
    have m₂ := ih₂ rfl assm₁ assm₂ path₂
    exact eqs ▸ .concat _ _ _ _ m₁ m₂

theorem matches_of_pathIn.star (eq : pushRegex nfa next (.star e) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs)
  (ih : ∀ {nfa next result cs},
    pushRegex nfa next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn result nfa.nodes.size result.val.start next cs →
    Expr.matches cs e) :
  (Expr.star e).matches cs := by
  open Compile.ProofData in
  let pd := Star.intro eq
  simp [pd.eq_result eq] at path
  apply matches_of_StarLoop ?_ (StarLoop.intro assm₁ assm₂ path)
  intro cs path

  -- TODO: might be reusable
  have path' : Star.nfaExpr.pathIn Star.nfaPlaceholder.nodes.size Star.nfaExpr.start Star.nfaPlaceholder.start cs := by
    simp [Star.nfaPlaceholder]

    have wf_expr := pd.wf_expr assm₁

    apply path.cast' wf_expr.start_lt (Nat.le_of_eq Star.size_eq_expr'.symm) wf_expr
    intro i h₁ h₂
    have := pd.get_ne_start i (Star.size_eq_expr' ▸ h₂) (Nat.ne_of_gt h₁)
    simp [this]
  have wf_placeholder := pd.wf_placeholder assm₁
  exact ih rfl wf_placeholder wf_placeholder.start_lt path'

theorem matches_of_pathIn_pushRegex (eq : pushRegex nfa next r = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (path : pathIn result nfa.nodes.size result.val.start next cs) :
  r.matches cs := by
  open Compile.ProofData in
  induction r generalizing nfa next cs with
  | empty =>
    let pd := Empty.intro eq
    simp [pd.eq_result eq] at path
    cases path with
    | last step => cases step <;> simp [pd.start_eq, pd.get_eq, Node.charStep, Node.εStep] at *
    | more step => cases step <;> simp [pd.start_eq, pd.get_eq, Node.charStep, Node.εStep] at *
  | epsilon =>
    let pd := Epsilon.intro eq
    simp [pd.eq_result eq] at path
    cases path with
    | last step =>
      cases step with
      | charStep _ _ step => simp [pd.start_eq, pd.get_eq, Node.charStep] at step
      | εStep _ _ step => exact .epsilon
    | more step rest =>
      have step := step.step
      simp [pd.start_eq, pd.get_eq, Node.charStep, Node.εStep] at step
      rw [step] at rest
      exact absurd assm₂ (Nat.not_lt_of_ge rest.le_left)
  | char c =>
    let pd := Char.intro eq
    simp [pd.eq_result eq] at path
    cases path with
    | last step =>
      cases step with
      | charStep _ _ step =>
        simp [pd.start_eq, pd.get_eq, Node.charStep] at step
        simp [step]
        exact .char _
      | εStep _ _ step => simp [pd.start_eq, pd.get_eq, Node.εStep] at step
    | more step rest =>
      have step := step.step
      simp [pd.start_eq, pd.get_eq, Node.charStep, Node.εStep] at step
      rw [step] at rest
      exact absurd assm₂ (Nat.not_lt_of_ge rest.le_left)
  | classes cls =>
    let pd := Classes.intro eq
    simp [pd.eq_result eq] at path
    cases path with
    | last step =>
      cases step with
      | charStep _ _ step =>
        simp [pd.start_eq, pd.get_eq, Node.charStep] at step
        exact .sparse _ _ step.left
      | εStep _ _ step => simp [pd.start_eq, pd.get_eq, Node.εStep] at step
    | more step rest =>
      have step := step.step
      simp [pd.start_eq, pd.get_eq, Node.charStep, Node.εStep] at step
      rw [step.right] at rest
      exact absurd assm₂ (Nat.not_lt_of_ge rest.le_left)
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
