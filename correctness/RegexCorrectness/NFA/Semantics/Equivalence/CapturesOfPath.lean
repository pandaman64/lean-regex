module

public import RegexCorrectness.NFA.Semantics.Equivalence.Basic
public import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Semantics.ProofData
import all Regex.NFA.Compile.Basic

namespace Regex.NFA

open Regex.Data (Expr)
open String (Pos)

variable {s : String} {nfa : NFA} {next e result} {pos pos' : Pos s} {update}

theorem captures_of_path.group {tag} (eq : nfa.pushRegex next (.group tag e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : result.Path nfa.size result.start pos next pos' update)
  (ih : ∀ {nfa : NFA} {next result} {pos pos' : Pos s} {update}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.size →
    result.Path nfa.size result.start pos next pos' update →
    ∃ groups, EquivUpdate groups update ∧ e.Captures pos pos' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.group tag e).Captures pos pos' groups := by
  open Compile.ProofData Group in
  let pd := Group.intro eq
  simp only [pd.eq_result eq] at path
  obtain ⟨updates, rfl, pathExpr⟩ := (pd.path_start_iff wf next_lt).mp path
  have wfClose := pd.wfClose wf next_lt
  have ⟨groups, eqv, c⟩ := ih rfl wfClose wfClose.start_lt pathExpr
  exact ⟨.group tag pos pos' groups, .group eqv, .group c⟩

theorem captures_of_path.alternate {e₁ e₂} (eq : nfa.pushRegex next (.alternate e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : result.Path nfa.size result.start pos next pos' update)
  (ih₁ : ∀ {nfa : NFA} {next result} {pos pos' : Pos s} {update}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.size →
    result.Path nfa.size result.start pos next pos' update →
    ∃ groups, EquivUpdate groups update ∧ e₁.Captures pos pos' groups)
  (ih₂ : ∀ {nfa : NFA} {next result} {pos pos' : Pos s} {update}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.size →
    result.Path nfa.size result.start pos next pos' update →
    ∃ groups, EquivUpdate groups update ∧ e₂.Captures pos pos' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.alternate e₁ e₂).Captures pos pos' groups := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp only [pd.eq_result eq] at path
  obtain path := (pd.path_start_iff wf next_lt).mp path
  cases path with
  | inl path₁ =>
    have ⟨groups, eqv, c⟩ := ih₁ rfl wf next_lt path₁
    exact ⟨groups, eqv, .alternateLeft c⟩
  | inr path₂ =>
    have wf₁ := wf₁ wf next_lt
    have ⟨groups, eqv, c⟩ := ih₂ rfl wf₁ (Nat.lt_trans next_lt pd.nfa₁_property) path₂
    exact ⟨groups, eqv, .alternateRight c⟩

theorem captures_of_path.concat {e₁ e₂} (eq : nfa.pushRegex next (.concat e₁ e₂) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : result.Path nfa.size result.start pos next pos' update)
  (ih₁ : ∀ {nfa : NFA} {next result} {pos pos' : Pos s} {update}, nfa.pushRegex next e₁ = result →
    nfa.WellFormed →
    next < nfa.size →
    result.Path nfa.size result.start pos next pos' update →
    ∃ groups, EquivUpdate groups update ∧ e₁.Captures pos pos' groups)
  (ih₂ : ∀ {nfa : NFA} {next result} {pos pos' : Pos s} {update}, nfa.pushRegex next e₂ = result →
    nfa.WellFormed →
    next < nfa.size →
    result.Path nfa.size result.start pos next pos' update →
    ∃ groups, EquivUpdate groups update ∧ e₂.Captures pos pos' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.concat e₁ e₂).Captures pos pos' groups := by
  open Compile.ProofData Concat in
  let pd := Concat.intro eq
  simp only [pd.eq_result eq] at path
  obtain ⟨pm, updates₁, updates₂, rfl, path₁, path₂⟩ := (pd.path_start_iff wf next_lt).mp path
  have wf₂ := wf₂ wf next_lt
  have ⟨groups₁, eqv₁, c₁⟩ := ih₁ rfl wf₂ wf₂.start_lt path₁
  have ⟨groups₂, eqv₂, c₂⟩ := ih₂ rfl wf next_lt path₂
  exact ⟨.concat groups₁ groups₂, .concat eqv₁ eqv₂, .concat c₁ c₂⟩

open Compile.ProofData Star in
theorem captures_of_path.star_of_loop [Star] {greedy : Bool} (loop : Loop pos pos' update)
  (ih : ∀ {pos pos' : Pos s} {update},
    nfa'.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start pos' update →
    ∃ groups, EquivUpdate groups update ∧ e.Captures pos pos' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.star greedy e).Captures pos pos' groups := by
  induction loop with
  | last step => exact ⟨.empty, .empty, .starEpsilon⟩
  | loop pathExpr _ ihLoop =>
    have ⟨groups₁, eqv₁, c₁⟩ := ih pathExpr
    have ⟨groups₂, eqv₂, c₂⟩ := ihLoop
    exact ⟨.concat groups₁ groups₂, .concat eqv₁ eqv₂, .starConcat c₁ c₂⟩

theorem captures_of_path.star {greedy e} (eq : nfa.pushRegex next (.star greedy e) = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : result.Path nfa.size result.start pos next pos' update)
  (ih : ∀ {nfa : NFA} {next result} {pos pos' : Pos s} {update}, nfa.pushRegex next e = result →
    nfa.WellFormed →
    next < nfa.size →
    result.Path nfa.size result.start pos next pos' update →
    ∃ groups, EquivUpdate groups update ∧ e.Captures pos pos' groups) :
  ∃ groups, EquivUpdate groups update ∧ (Expr.star greedy e).Captures pos pos' groups := by
  open Compile.ProofData Star in
  let pd := Star.intro eq
  simp only [pd.eq_result eq] at path
  have h := (pd.path_start_iff next_lt).mp path
  match h with
  | .inl ⟨hp, hupdate⟩ =>
    subst pos' update
    exact ⟨.empty, .empty, .starEpsilon⟩
  | .inr path =>
    have loop := Loop.intro wf next_lt path
    apply captures_of_path.star_of_loop loop

    intro pos pos' update path
    have path := castToExpr wf path
    have wfPlaceholder := wfPlaceholder wf
    -- Since v4.29.0, many tactics and defeqs cannot reduce `Star.into`. So we do it here manually.
    have : e = pd.e' := by with_reducible_and_instances rfl
    exact ih (by grind) wfPlaceholder wfPlaceholder.start_lt path

public theorem captures_of_path (eq : nfa.pushRegex next e = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : result.Path nfa.size result.start pos next pos' update) :
  ∃ groups, EquivUpdate groups update ∧ e.Captures pos pos' groups := by
  open Compile.ProofData in
  induction e generalizing nfa next result pos pos' update with
  | empty =>
    let pd := Empty.intro eq
    simp only [pd.eq_result eq] at path
    exact absurd path pd.not_path_start
  | epsilon =>
    let pd := Epsilon.intro eq
    simp only [pd.eq_result eq] at path
    have := (pd.path_start_iff next_lt).mp path
    simp [this]
    exact ⟨.empty, .empty, .epsilon⟩
  | anchor a =>
    let pd := Anchor.intro eq
    simp only [pd.eq_result eq] at path
    obtain ⟨_, rfl, rfl, test⟩:= (pd.path_start_iff next_lt).mp path
    exact ⟨.empty, .empty, .anchor test⟩
  | char c =>
    let pd := Char.intro eq
    simp only [pd.eq_result eq] at path
    obtain ⟨_, rfl, ne, rfl, rfl⟩ := (pd.path_start_iff next_lt).mp path
    exact ⟨.empty, .empty, .char ne rfl⟩
  | classes cs =>
    let pd := Classes.intro eq
    simp only [pd.eq_result eq] at path
    obtain ⟨_, rfl, ne, rfl, mem⟩ := (pd.path_start_iff next_lt).mp path
    exact ⟨.empty, .empty, .sparse ne mem⟩
  | group tag e ih => exact captures_of_path.group eq wf next_lt path ih
  | alternate e₁ e₂ ih₁ ih₂ => exact captures_of_path.alternate eq wf next_lt path ih₁ ih₂
  | concat e₁ e₂ ih₁ ih₂ => exact captures_of_path.concat eq wf next_lt path ih₁ ih₂
  | star greedy e ih => exact captures_of_path.star eq wf next_lt path ih

public theorem captures_of_path_compile (eq : compile e = nfa) (path : nfa.Path 1 nfa.start pos 0 pos' update) :
  ∃ groups, EquivUpdate groups update ∧ e.Captures pos pos' groups := by
  simp [←eq, compile] at path
  exact captures_of_path rfl done_WellFormed (by decide) path

end Regex.NFA
