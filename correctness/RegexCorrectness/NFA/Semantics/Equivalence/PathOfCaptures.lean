import RegexCorrectness.NFA.Semantics.Equivalence.Basic
import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Semantics.ProofData

set_option autoImplicit false

namespace Regex.NFA

open Regex.Data (Expr CaptureGroups)
open String (Pos)

variable {s : String} {nfa : NFA} {next e result} {pos pos' : Pos s} {groups : CaptureGroups s}

theorem path_of_captures.group {tag} (eq : nfa.pushRegex next (.group tag e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups update ∧ result.Path nfa.nodes.size result.start pos next pos' update) :
  ∃ update, EquivUpdate (.group tag pos pos' groups) update ∧ result.Path nfa.nodes.size result.start pos next pos' update := by
  open Compile.ProofData Group in
  let pd := Group.intro eq
  simp [eq_result eq]

  have wf_close := wf_close wf next_lt
  have ⟨update, eqv, path⟩ := ih (result := nfaExpr) rfl wf_close wf_close.start_lt
  exists (2 * tag, pos) :: update ++ [(2 * tag + 1, pos')], .group eqv

  have stepOpen : nfa'.Step nfa.nodes.size nfa'.start pos nfaExpr.start pos (.some (2 * tag, pos)) := by
    apply step_start_iff.mpr
    exact ⟨rfl, rfl, rfl⟩
  have path := castFromExpr path
  have path : nfa'.Path nfa.nodes.size nfaExpr.start pos nfaClose.start pos' update :=
    path.liftBound (by simp [Group.nfaClose]; exact Nat.le_succ _)
  have pathClose : nfa'.Path nfa.nodes.size nfaClose.start pos' next pos' [(2 * tag + 1, pos')] := by
    have stepClose : nfa'.Step nfa.nodes.size nfaClose.start pos' next pos' (.some (2 * tag + 1, pos')) := by
      apply step_close_iff.mpr
      exact ⟨rfl, rfl, rfl⟩
    exact .last stepClose
  exact .more stepOpen (path.trans pathClose)

theorem path_of_captures.alternateLeft {e₁ e₂} (eq : nfa.pushRegex next (.alternate e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups update ∧ result.Path nfa.nodes.size result.start pos next pos' update) :
  ∃ update, EquivUpdate groups update ∧ result.Path nfa.nodes.size result.start pos next pos' update := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [eq_result eq]

  have ⟨update, eqv, path⟩ := ih (result := nfa₁) rfl wf next_lt
  exists update, eqv

  have step : nfa'.Step nfa.nodes.size nfa'.start pos nfa₁.start pos .none := by
    apply step_start_iff.mpr
    simp
  have path := castFrom₁ path
  exact .more step path

theorem path_of_captures.alternateRight {e₁ e₂} (eq : nfa.pushRegex next (.alternate e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups update ∧ result.Path nfa.nodes.size result.start pos next pos' update) :
  ∃ update, EquivUpdate groups update ∧ result.Path nfa.nodes.size result.start pos next pos' update := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [eq_result eq]

  have wf₁ := wf₁ wf next_lt
  have ⟨update, eqv, path⟩ := ih (result := nfa₂) rfl wf₁ (Nat.lt_trans next_lt nfa₁_property)
  exists update, eqv

  have step : nfa'.Step nfa.nodes.size nfa'.start pos nfa₂.start pos .none := by
    apply step_start_iff.mpr
    simp
  have path := castFrom₂ (path.liftBound (Nat.le_of_lt nfa₁_property))
  exact .more step path

theorem path_of_captures.concat {pos'' e₁ e₂ groups₁ groups₂} (eq : nfa.pushRegex next (.concat e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih₁ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₁ update ∧ result.Path nfa.nodes.size result.start pos next pos' update)
  (ih₂ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₂ update ∧ result.Path nfa.nodes.size result.start pos' next pos'' update) :
  ∃ update, EquivUpdate (.concat groups₁ groups₂) update ∧ result.Path nfa.nodes.size result.start pos next pos'' update := by
  open Compile.ProofData Concat in
  let pd := Concat.intro eq
  simp [pd.eq_result eq]

  have wf₂ := wf₂ wf next_lt
  have ⟨update₁, eqv₁, path₁⟩ := ih₁ eq_push.symm wf₂ wf₂.start_lt
  have ⟨update₂, eqv₂, path₂⟩ := ih₂ (result := nfa₂) rfl wf next_lt
  exists update₁ ++ update₂, .concat eqv₁ eqv₂

  have path₂ := castFrom₂ path₂
  exact (path₁.liftBound (Nat.le_of_lt nfa₂_property)).trans path₂

theorem path_of_captures.starConcat {pos'' greedy e groups₁ groups₂} (eq : nfa.pushRegex next (.star greedy e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (ih₁ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₁ update ∧ result.Path nfa.nodes.size result.start pos next pos' update)
  (ih₂ : ∀ {nfa : NFA} {next result}, nfa.pushRegex next (.star greedy e) = result →
    nfa.WellFormed →
    next < nfa.nodes.size →
    ∃ update, EquivUpdate groups₂ update ∧ result.Path nfa.nodes.size result.start pos' next pos'' update) :
  ∃ update, EquivUpdate (.concat groups₁ groups₂) update ∧ result.Path nfa.nodes.size result.start pos next pos'' update := by
  open Compile.ProofData Star in
  let pd := Star.intro eq
  simp [pd.eq_result eq]

  have wf_placeholder := wf_placeholder wf
  have ⟨update₁, eqv₁, path₁⟩ := ih₁ (result := nfaExpr) rfl wf_placeholder wf_placeholder.start_lt
  have ⟨update₂, eqv₂, path₂⟩ := ih₂ (result := nfa') rfl wf next_lt
  exists update₁ ++ update₂, .concat eqv₁ eqv₂

  have start_eq_placeholder : nfaPlaceholder.start = nfa'.start := by
    simp [nfaPlaceholder, start_eq]
  have path₁ : nfa'.Path nfa.nodes.size nfaExpr.start pos nfa'.start pos' update₁ :=
    start_eq_placeholder ▸ (castFromExpr path₁).liftBound (by simp [nfaPlaceholder]; exact Nat.le_succ _)
  have step : nfa'.Step nfa.nodes.size nfa'.start pos nfaExpr.start pos .none :=
    if h : pd.greedy then
      .splitLeft (j₂ := next) (by simp [start_eq]; exact Nat.le_refl _) (wf' wf next_lt).start_lt (by simp [start_eq, get_start, splitNode, h]; rfl)
    else
      .splitRight (j₁ := next) (by simp [start_eq]; exact Nat.le_refl _) (wf' wf next_lt).start_lt (by simp [start_eq, get_start, splitNode, h]; rfl)

  exact (Path.more step path₁).trans path₂

theorem path_of_captures (eq : nfa.pushRegex next e = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (c : e.Captures pos pos' groups) :
  ∃ update, EquivUpdate groups update ∧ result.Path nfa.nodes.size result.start pos next pos' update := by
  open Compile.ProofData in
  induction c generalizing nfa next result with
  | char ne hc =>
    let pd := Char.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    exact ⟨rfl, rfl, ne, rfl, hc⟩
  | sparse ne mem =>
    let pd := Classes.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    exact ⟨rfl, rfl, ne, rfl, mem⟩
  | epsilon =>
    let pd := Epsilon.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    trivial
  | anchor h =>
    let pd := Anchor.intro eq
    exists [], .empty
    simp [pd.eq_result eq]
    apply (pd.path_start_iff next_lt).mpr
    trivial
  | group c ih => exact path_of_captures.group eq wf next_lt ih
  | alternateLeft c ih => exact path_of_captures.alternateLeft eq wf next_lt ih
  | alternateRight c ih => exact path_of_captures.alternateRight eq wf next_lt ih
  | concat _ _ ih₁ ih₂ => exact path_of_captures.concat eq wf next_lt ih₁ ih₂
  | @starEpsilon pos _ _ =>
    let pd := Star.intro eq
    exists [], .empty
    simp [pd.eq_result eq]

    have step : nfa'.Step nfa.nodes.size nfa'.start pos next pos .none := by
      apply (pd.step_start_iff).mpr
      exact ⟨.inr rfl, rfl, rfl⟩
    exact .last step
  | starConcat c₁ _ ih₁ ih₂ => exact path_of_captures.starConcat eq wf next_lt ih₁ ih₂

theorem path_of_captures_compile (eq : compile e = nfa) (c : e.Captures pos pos' groups) :
  ∃ update, EquivUpdate groups update ∧ nfa.Path 1 nfa.start pos 0 pos' update := by
  simp [←eq, compile]
  exact path_of_captures rfl done_WellFormed (by decide) c

end Regex.NFA
