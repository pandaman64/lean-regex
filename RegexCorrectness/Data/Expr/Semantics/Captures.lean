import Regex.Data.Expr
import RegexCorrectness.Data.Span
import RegexCorrectness.Data.Expr.Semantics.Matches

set_option autoImplicit false

namespace Regex.Data

inductive Expr.Captures : Span → Span → List (Nat × String.Pos × String.Pos) → Expr → Prop where
  | char {l m r} (c : Char) : Expr.Captures ⟨l, m, c :: r⟩ ⟨l, c :: m, r⟩ [] (.char c)
  | sparse {l m c r cs} (h : c ∈ cs) : Expr.Captures ⟨l, m, c :: r⟩ ⟨l, c :: m, r⟩ [] (.classes cs)
  | epsilon {span} : Expr.Captures span span [] .epsilon
  | group {span span' groups tag e} (cap : Expr.Captures span span' groups e) :
    Expr.Captures span span' (groups ++ [(tag, span.curr, span'.curr)]) (.group tag e)
  | alternateLeft {span span' groups e₁ e₂} (cap : Expr.Captures span span' groups e₁) :
    Expr.Captures span span' groups (.alternate e₁ e₂)
  | alternateRight {span span' groups e₁ e₂} (cap : Expr.Captures span span' groups e₂) :
    Expr.Captures span span' groups (.alternate e₁ e₂)
  | concat {span span' span'' groups₁ groups₂ e₁ e₂} (cap₁ : Expr.Captures span span' groups₁ e₁) (cap₂ : Expr.Captures span' span'' groups₂ e₂) :
    Expr.Captures span span'' (groups₁ ++ groups₂) (.concat e₁ e₂)
  | starEpsilon {span e} : Expr.Captures span span [] (.star e)
  | starConcat {span span' span'' groups groups' e} (cap₁ : Expr.Captures span span' groups e) (cap₂ : Expr.Captures span' span'' groups' (.star e)) :
    Expr.Captures span span'' (groups ++ groups') (.star e)

theorem captures_of_matches {l n₁ n₂ r e} (m : Expr.matches n₂ e) :
  ∃ groups, Expr.Captures ⟨l, n₁, n₂ ++ r⟩ ⟨l, n₂.reverse ++ n₁, r⟩ groups e := by
  induction m generalizing n₁ r with
  | char c => exact ⟨[], .char c⟩
  | sparse cs c mem => exact ⟨[], .sparse mem⟩
  | epsilon => exact ⟨[], .epsilon⟩
  | group m ih =>
    have ⟨groups, cap⟩ := @ih n₁ r
    exact ⟨groups ++ [_], .group cap⟩
  | alternateLeft m ih =>
    have ⟨groups, cap⟩ := @ih n₁ r
    exact ⟨groups, .alternateLeft cap⟩
  | alternateRight m ih =>
    have ⟨groups, cap⟩ := @ih n₁ r
    exact ⟨groups, .alternateRight cap⟩
  | concat cs₁ cs₂ _ _ m₁ m₂ ih₁ ih₂ =>
    have ⟨groups₁, cap₁⟩ := @ih₁ n₁ (cs₂ ++ r)
    have ⟨groups₂, cap₂⟩ := @ih₂ (cs₁.reverse ++ n₁) r
    exact ⟨groups₁ ++ groups₂, by simp; exact .concat cap₁ cap₂⟩
  | starEpsilon => exact ⟨[], .starEpsilon⟩
  | starConcat cs₁ cs₂ _ _ _ ih₁ ih₂ =>
    have ⟨groups₁, cap₁⟩ := @ih₁ n₁ (cs₂ ++ r)
    have ⟨groups₂, cap₂⟩ := @ih₂ (cs₁.reverse ++ n₁) r
    exact ⟨groups₁ ++ groups₂, by simp; exact .starConcat cap₁ cap₂⟩

theorem matches_of_captures {span span' groups e} (c : Expr.Captures span span' groups e) :
  ∃ n, Expr.matches n e ∧ span'.l = span.l ∧ span'.m = n.reverse ++ span.m ∧ n ++ span'.r = span.r := by
  induction c with
  | char c => exact ⟨[c], .char c, rfl, rfl, rfl⟩
  | sparse mem => exact ⟨[_], .sparse _ _ mem, rfl, rfl, rfl⟩
  | epsilon => exact ⟨[], .epsilon, rfl, rfl, rfl⟩
  | group _ ih =>
    have ⟨n, m, _⟩ := ih
    exists n, .group m
  | alternateLeft _ ih =>
    have ⟨n, m, _⟩ := ih
    exists n, .alternateLeft m
  | alternateRight _ ih =>
    have ⟨n, m, _⟩ := ih
    exists n, .alternateRight m
  | concat _ _ ih₁ ih₂ =>
    have ⟨n₁, m₁, h₁⟩ := ih₁
    have ⟨n₂, m₂, h₂⟩ := ih₂
    exists n₁ ++ n₂, .concat _ _ _ _ m₁ m₂
    simp [h₁, h₂]
  | starEpsilon => exact ⟨[], .starEpsilon, rfl, rfl, rfl⟩
  | starConcat _ _ ih₁ ih₂ =>
    have ⟨n₁, m₁, h₁⟩ := ih₁
    have ⟨n₂, m₂, h₂⟩ := ih₂
    exists n₁ ++ n₂, .starConcat _ _ _ m₁ m₂
    simp [h₁, h₂]

end Regex.Data
