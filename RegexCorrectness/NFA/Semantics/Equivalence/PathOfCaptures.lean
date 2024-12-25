import RegexCorrectness.NFA.Semantics.Equivalence.Basic

set_option autoImplicit false

namespace Regex.NFA

open Regex.Data (Expr)

variable {nfa : NFA} {next e result span span' groups}

theorem path_of_captures.group {tag} (eq : nfa.pushRegex next (.group tag e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update) :
  ∃ update, EquivUpdate ((tag, span.curr, span'.curr) :: groups) update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update := by
  open Compile.ProofData Group in
  let pd := Group.intro eq
  simp [eq_result eq]

  have wf_close := wf_close wf next_lt
  have ⟨update, eqv, path⟩ := ih (result := ⟨nfaExpr, _⟩) rfl wf_close wf_close.start_lt
  exists (2 * tag, span.curr) :: update ++ [(2 * tag + 1, span'.curr)], .group eqv

  have stepOpen : nfa'.Step nfa.nodes.size nfa'.start span nfaExpr.start span (.some (2 * tag, span.curr)) := by
    apply step_start_iff.mpr
    trivial
  have path := castFromExpr path
  have path : nfa'.Path nfa.nodes.size nfaExpr.start span nfaClose.start span' update :=
    path.liftBound (by simp [Group.nfaClose]; exact Nat.le_succ _)
  have pathClose : nfa'.Path nfa.nodes.size nfaClose.start span' next span' [(2 * tag + 1, span'.curr)] := by
    have stepClose : nfa'.Step nfa.nodes.size nfaClose.start span' next span' (.some (2 * tag + 1, span'.curr)) := by
      apply step_close_iff.mpr
      trivial
    exact .last stepClose
  exact .more stepOpen (path.trans pathClose)

theorem path_of_captures.alternateLeft {e₁ e₂} (eq : nfa.pushRegex next (.alternate e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update) :
  ∃ update, EquivUpdate groups update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [eq_result eq]

  have ⟨update, eqv, path⟩ := ih (result := ⟨nfa₁, _⟩) rfl wf next_lt
  exists update, eqv

  have step : nfa'.Step nfa.nodes.size nfa'.start span nfa₁.start span .none := by
    apply step_start_iff.mpr
    simp
  have path := castFrom₁ path
  exact .more step path

theorem path_of_captures.alternateRight {e₁ e₂} (eq : nfa.pushRegex next (.alternate e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update) :
  ∃ update, EquivUpdate groups update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [eq_result eq]

  have wf₁ := wf₁ wf next_lt
  have ⟨update, eqv, path⟩ := ih (result := ⟨nfa₂, _⟩) rfl wf₁ (Nat.lt_trans next_lt nfa₁_property)
  exists update, eqv

  have step : nfa'.Step nfa.nodes.size nfa'.start span nfa₂.start span .none := by
    apply step_start_iff.mpr
    simp
  have path := castFrom₂ (path.liftBound (Nat.le_of_lt nfa₁_property))
  exact .more step path

theorem path_of_captures.concat {e₁ e₂ span span' span'' groups₁ groups₂} (eq : nfa.pushRegex next (.concat e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih₁ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₁ update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update)
  (ih₂ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₂ update ∧ result.val.Path nfa.nodes.size result.val.start span' next span'' update) :
  ∃ update, EquivUpdate (groups₁ ++ groups₂) update ∧ result.val.Path nfa.nodes.size result.val.start span next span'' update := by
  open Compile.ProofData Concat in
  let pd := Concat.intro eq
  simp [pd.eq_result eq]

  have wf₂ := wf₂ wf next_lt
  have ⟨update₁, eqv₁, path₁⟩ := ih₁ (result := ⟨nfa', size₂_lt⟩) (Subtype.eq eq_push.symm) wf₂ wf₂.start_lt
  have ⟨update₂, eqv₂, path₂⟩ := ih₂ (result := ⟨nfa₂, _⟩) rfl wf next_lt
  simp at path₁ path₂
  exists update₁ ++ update₂, .concat eqv₁ eqv₂

  have path₂ := castFrom₂ path₂
  exact (path₁.liftBound (Nat.le_of_lt nfa₂_property)).trans path₂

theorem path_of_captures.starConcat {e span span' span'' groups₁ groups₂} (eq : nfa.pushRegex next (.star e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih₁ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₁ update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update)
  (ih₂ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next (.star e) = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₂ update ∧ result.val.Path nfa.nodes.size result.val.start span' next span'' update) :
  ∃ update, EquivUpdate (groups₁ ++ groups₂) update ∧ result.val.Path nfa.nodes.size result.val.start span next span'' update := by
  open Compile.ProofData Star in
  let pd := Star.intro eq
  simp [pd.eq_result eq]

  have wf_placeholder := wf_placeholder wf
  have ⟨update₁, eqv₁, path₁⟩ := ih₁ (result := ⟨nfaExpr, _⟩) rfl wf_placeholder wf_placeholder.start_lt
  have ⟨update₂, eqv₂, path₂⟩ := ih₂ (result := ⟨nfa', _⟩) rfl wf next_lt
  simp at path₁ path₂
  exists update₁ ++ update₂, .concat eqv₁ eqv₂

  have start_eq_placeholder : nfaPlaceholder.start = nfa'.start := by
    simp [nfaPlaceholder, start_eq]
  have path₁ : nfa'.Path nfa.nodes.size nfaExpr.start span nfa'.start span' update₁ :=
    start_eq_placeholder ▸ (castFromExpr path₁).liftBound (by simp [nfaPlaceholder]; exact Nat.le_succ _)
  have step : nfa'.Step nfa.nodes.size nfa'.start span nfaExpr.start span .none :=
    .splitLeft (j₂ := next) (by simp [start_eq]; exact Nat.le_refl _) (wf' wf next_lt).start_lt (by simp [start_eq, get_start]; rfl)

  exact (Path.more step path₁).trans path₂

theorem path_of_captures (eq : nfa.pushRegex next e = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (c : e.Captures span span' groups) :
  ∃ update, EquivUpdate groups update ∧ result.val.Path nfa.nodes.size result.val.start span next span' update := by
  open Compile.ProofData in
  induction c generalizing nfa next with
  | @char l c r =>
    let pd := Char.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    exists r
  | @sparse l c r cs =>
    let pd := Classes.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    exists c, r
  | @epsilon l r =>
    let pd := Epsilon.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    trivial
  | group _ ih => exact path_of_captures.group eq wf next_lt ih
  | alternateLeft _ ih => exact path_of_captures.alternateLeft eq wf next_lt ih
  | alternateRight _ ih => exact path_of_captures.alternateRight eq wf next_lt ih
  | concat _ _ ih₁ ih₂ => exact path_of_captures.concat eq wf next_lt ih₁ ih₂
  | @starEpsilon l r e =>
    let pd := Star.intro eq
    exists [], .empty
    simp [pd.eq_result eq]

    have step : nfa'.Step nfa.nodes.size nfa'.start ⟨l, [], r⟩ next ⟨l, [], r⟩ .none := by
      apply (pd.step_start_iff).mpr
      simp
      exact .inr rfl
    exact .last step
  | starConcat _ _ ih₁ ih₂ => exact path_of_captures.starConcat eq wf next_lt ih₁ ih₂

end Regex.NFA
