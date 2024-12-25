import RegexCorrectness.NFA.Semantics.Equivalence.Basic

set_option autoImplicit false

namespace Regex.NFA

open Regex.Data (Expr)

variable {nfa : NFA} {next e result span span' update}

theorem captures_of_path.group {tag} (eq : nfa.pushRegex next (.group tag e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : result.val.Path nfa.nodes.size result.val.start span next span' update)
  (ih : ∀ {nfa : NFA} {next result span span' update}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    result.val.Path nfa.nodes.size result.val.start span next span' update →
    ∃ groups, EquivUpdate groups update ∧ e.Captures span span' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.group tag e).Captures span span' groups := by
  open Compile.ProofData Group in
  let pd := Group.intro eq
  simp [pd.eq_result eq] at path

  cases path with
  | last step =>
    have ⟨eqnext, _, _⟩ := step_start_iff.mp step
    have ge := ge_pushRegex_start (result := ⟨nfaExpr, _⟩) rfl
    simp [←eqnext, nfaClose] at ge
    have : next < pd.nfa.nodes.size := next_lt
    omega
  | @more i span j spanm k span'' update updates step rest  =>
    have ⟨hj, hspan, hupdate⟩ := step_start_iff.mp step
    simp [hupdate]
    simp [hj, hspan] at rest

    have rest := castToExpr wf next_lt rest
    have next_lt_close : next < nfaClose.nodes.size := by
      simp [nfaClose]
      exact Nat.lt_trans next_lt (Nat.lt_add_one _)
    have ge_expr_start : nfaClose.nodes.size ≤ nfaExpr.start := ge_pushRegex_start rfl
    have ne_next : next ≠ nfaClose.start := by
      simp [nfaClose]
      exact Nat.ne_of_lt next_lt
    have ⟨spanm, updateExpr, updateClose, equ, pathExpr, pathClose⟩ :=
      rest.path_next_of_ne (result := ⟨nfaExpr, _⟩) rfl next_lt_close ge_expr_start ne_next
    simp at pathExpr pathClose

    have wf_close := wf_close wf next_lt
    have ⟨groupExpr, eqv, c⟩ := ih (result := ⟨nfaExpr, _⟩) rfl wf_close wf_close.start_lt pathExpr

    have : nfaExpr[nfaClose.start]'size_lt_nfa_expr = nfa'[nfaClose.start]'size_lt := by
      simp [nfaClose, get_close_expr, get_close]
    cases pathClose with
    | last step =>
      have ⟨_, hspan, hupdate⟩ := step_close_iff.mp (step.cast this)
      rw [←hspan] at c
      simp [equ, hupdate, ←hspan]
      exact ⟨(tag, span.curr, span'.curr) :: groupExpr, .group eqv, .group c⟩
    | more step rest =>
      have ⟨hj, _, _⟩ := step_close_iff.mp (step.cast this)
      have : nfa.nodes.size ≤ next := show nfa.nodes.size ≤ pd.next from hj ▸ rest.ge
      omega

theorem captures_of_path.alternate {e₁ e₂} (eq : nfa.pushRegex next (.alternate e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : result.val.Path nfa.nodes.size result.val.start span next span' update)
  (ih₁ : ∀ {nfa : NFA} {next result span span' update}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    result.val.Path nfa.nodes.size result.val.start span next span' update →
    ∃ groups, EquivUpdate groups update ∧ e₁.Captures span span' groups)
  (ih₂ : ∀ {nfa : NFA} {next result span span' update}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    result.val.Path nfa.nodes.size result.val.start span next span' update →
    ∃ groups, EquivUpdate groups update ∧ e₂.Captures span span' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.alternate e₁ e₂).Captures span span' groups := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [pd.eq_result eq] at path

  cases path with
  | last step =>
    have := step_start_iff.mp step
    have : next < nfa₁.start := Nat.lt_of_lt_of_le next_lt (ge_pushRegex_start rfl)
    have : next < nfa₂.start := Nat.lt_of_lt_of_le (Nat.lt_trans next_lt nfa₁_property) (ge_pushRegex_start rfl)
    omega
  | @more i span j spanm k span'' update updates step rest =>
    have ⟨hj, hspan, hupdate⟩ := step_start_iff.mp step
    simp [hupdate]
    cases hj with
    | inl hj =>
      simp [hj, hspan] at rest
      have rest := castTo₁ wf next_lt rest
      have ⟨groups, eqv, c⟩ := ih₁ rfl wf next_lt rest
      exact ⟨groups, eqv, .alternateLeft c⟩
    | inr hj =>
      simp [hj, hspan] at rest

      have rest := castTo₂ wf next_lt rest
      have rest : nfa₂.Path nfa₁.nodes.size nfa₂.start span next span' updates := by
        apply rest.liftBound' (ge_pushRegex_start rfl)
        intro i span j span' update gei gej step
        cases (step.liftBound' gei).eq_or_ge_of_pushRegex with
        | inl eq =>
          have : nfa.nodes.size ≤ next := show nfa.nodes.size ≤ pd.next from eq ▸ gej
          omega
        | inr ge => exact ge

      have wf₁ := wf₁ wf next_lt
      have ⟨groups, eqv, c⟩ := ih₂ rfl wf₁ (Nat.lt_trans next_lt nfa₁_property) rest
      exact ⟨groups, eqv, .alternateRight c⟩

theorem captures_of_path.concat {e₁ e₂} (eq : nfa.pushRegex next (.concat e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : result.val.Path nfa.nodes.size result.val.start span next span' update)
  (ih₁ : ∀ {nfa : NFA} {next result span span' update}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    result.val.Path nfa.nodes.size result.val.start span next span' update →
    ∃ groups, EquivUpdate groups update ∧ e₁.Captures span span' groups)
  (ih₂ : ∀ {nfa : NFA} {next result span span' update}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    result.val.Path nfa.nodes.size result.val.start span next span' update →
    ∃ groups, EquivUpdate groups update ∧ e₂.Captures span span' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.concat e₁ e₂).Captures span span' groups := by
  open Compile.ProofData Concat in
  let pd := Concat.intro eq
  simp [pd.eq_result eq] at path
  have next_lt₂ : next < nfa₂.nodes.size := Nat.lt_trans next_lt nfa₂_property
  have ge_start : nfa₂.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have ne_next : next ≠ nfa₂.start := Nat.ne_of_lt (Nat.lt_of_lt_of_le next_lt (ge_pushRegex_start rfl))
  have ⟨spanm, update₁, update₂, equ, path₁, path₂⟩ := path.path_next_of_ne rfl next_lt₂ ge_start ne_next

  have wf₂ := wf₂ wf next_lt
  have ⟨group₁, eqv₁, c₁⟩ := ih₁ rfl wf₂ wf₂.start_lt path₁
  have ⟨group₂, eqv₂, c₂⟩ := ih₂ rfl wf next_lt (castTo₂ wf next_lt path₂)
  exact ⟨group₁ ++ group₂, equ ▸ .concat eqv₁ eqv₂, .concat c₁ c₂⟩

open Compile.ProofData Star in
theorem captures_of_path.star_of_loop [Star] (loop : Loop span span' update)
  (ih : ∀ {span span' update},
    nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start span' update →
    ∃ groups, EquivUpdate groups update ∧ e.Captures span span' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.star e).Captures span span' groups := by
  induction loop with
  | last => exact ⟨[], .empty, .starEpsilon⟩
  | loop pathExpr _ ihLoop =>
    have ⟨groups₁, eqv₁, c₁⟩ := ih pathExpr
    have ⟨groups₂, eqv₂, c₂⟩ := ihLoop
    exact ⟨groups₁ ++ groups₂, .concat eqv₁ eqv₂, .starConcat c₁ c₂⟩

theorem captures_of_path.star {e} (eq : nfa.pushRegex next (.star e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : result.val.Path nfa.nodes.size result.val.start span next span' update)
  (ih : ∀ {nfa : NFA} {next result span span' update}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    result.val.Path nfa.nodes.size result.val.start span next span' update →
    ∃ groups, EquivUpdate groups update ∧ e.Captures span span' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.star e).Captures span span' groups := by
  open Compile.ProofData Star in
  let pd := Star.intro eq
  simp [pd.eq_result eq] at path
  have loop := Loop.intro wf next_lt path
  apply captures_of_path.star_of_loop loop

  intro span span' update path
  have path := castToExpr wf path
  have wf_placeholder := wf_placeholder wf
  exact ih rfl wf_placeholder wf_placeholder.start_lt path

theorem captures_of_path (eq : nfa.pushRegex next e = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : result.val.Path nfa.nodes.size result.val.start span next span' update) :
  ∃ groups, EquivUpdate groups update ∧ e.Captures span span' groups := by
  open Compile.ProofData in
  induction e generalizing nfa next span span' update with
  | empty =>
    let pd := Empty.intro eq
    simp [pd.eq_result eq] at path
    exact absurd path pd.not_path_start
  | epsilon =>
    let pd := Epsilon.intro eq
    simp [pd.eq_result eq] at path
    have := (pd.path_start_iff next_lt).mp path
    simp [this]
    exact ⟨[], .empty, .epsilon⟩
  | char c =>
    let pd := Char.intro eq
    simp [pd.eq_result eq] at path
    have ⟨r, eqr, eq⟩ := (pd.path_start_iff next_lt).mp path
    simp [eq]
    have cap : Expr.Captures ⟨span.l, span.m, pd.c :: r⟩ ⟨span.l, pd.c :: span.m, r⟩ [] (.char c) := .char c
    have eqs : span = ⟨span.l, span.m, pd.c :: r⟩ := by
      rw [←eqr]
    exact ⟨[], .empty, eqs ▸ cap⟩
  | classes cs =>
    let pd := Classes.intro eq
    simp [pd.eq_result eq] at path
    have ⟨c, r, eqcr, mem, eq⟩ := (pd.path_start_iff next_lt).mp path
    simp [eq]
    have cap : Expr.Captures ⟨span.l, span.m, c :: r⟩ ⟨span.l, c :: span.m, r⟩ [] (.classes cs) := .sparse mem
    have eqs : span = ⟨span.l, span.m, c :: r⟩ := by
      rw [←eqcr]
    exact ⟨[], .empty, eqs ▸ cap⟩
  | group tag e ih => exact captures_of_path.group eq wf next_lt path ih
  | alternate e₁ e₂ ih₁ ih₂ => exact captures_of_path.alternate eq wf next_lt path ih₁ ih₂
  | concat e₁ e₂ ih₁ ih₂ => exact captures_of_path.concat eq wf next_lt path ih₁ ih₂
  | star e ih => exact captures_of_path.star eq wf next_lt path ih

theorem captures_of_path_compile (eq : compile e = nfa) (path : nfa.Path 1 nfa.start span 0 span' update) :
  ∃ groups, EquivUpdate groups update ∧ e.Captures span span' groups := by
  simp [←eq, compile] at path
  exact captures_of_path rfl done_WellFormed (by decide) path

end Regex.NFA
