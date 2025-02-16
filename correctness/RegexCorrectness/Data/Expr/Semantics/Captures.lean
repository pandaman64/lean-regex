import Regex.Data.Expr
import RegexCorrectness.Data.Span
import RegexCorrectness.Data.Expr.Semantics.CaptureGroups

set_option autoImplicit false

namespace Regex.Data

inductive Expr.Captures : Span → Span → CaptureGroups → Expr → Prop where
  | char {l m r} (c : Char) : Expr.Captures ⟨l, m, c :: r⟩ ⟨l, c :: m, r⟩ .empty (.char c)
  | sparse {l m c r cs} (h : c ∈ cs) : Expr.Captures ⟨l, m, c :: r⟩ ⟨l, c :: m, r⟩ .empty (.classes cs)
  | epsilon {span} : Expr.Captures span span .empty .epsilon
  | anchor {span anchor} (h : anchor.test span.iterator) : Expr.Captures span span .empty (.anchor anchor)
  | group {span span' groups tag e} (cap : Expr.Captures span span' groups e) :
    Expr.Captures span span' (.group tag span.curr span'.curr groups) (.group tag e)
  | alternateLeft {span span' groups e₁ e₂} (cap : Expr.Captures span span' groups e₁) :
    Expr.Captures span span' groups (.alternate e₁ e₂)
  | alternateRight {span span' groups e₁ e₂} (cap : Expr.Captures span span' groups e₂) :
    Expr.Captures span span' groups (.alternate e₁ e₂)
  | concat {span span' span'' groups₁ groups₂ e₁ e₂} (cap₁ : Expr.Captures span span' groups₁ e₁) (cap₂ : Expr.Captures span' span'' groups₂ e₂) :
    Expr.Captures span span'' (.concat groups₁ groups₂) (.concat e₁ e₂)
  | starEpsilon {span e} : Expr.Captures span span .empty (.star e)
  | starConcat {span span' span'' groups₁ groups₂ e} (cap₁ : Expr.Captures span span' groups₁ e) (cap₂ : Expr.Captures span' span'' groups₂ (.star e)) :
    Expr.Captures span span'' (.concat groups₁ groups₂) (.star e)

theorem Expr.Captures.span_eq {span span' groups e} (c : Expr.Captures span span' groups e) :
  ∃ m, span.l = span'.l ∧ m.reverse ++ span.m = span'.m ∧ span.r = m ++ span'.r := by
  induction c with
  | char c => exists [c]
  | @sparse l m c r cs mem => exists [c]
  | epsilon => exists []
  | anchor h => exists []
  | group _ ih => exact ih
  | alternateLeft _ ih => exact ih
  | alternateRight _ ih => exact ih
  | concat _ _ ih₁ ih₂ =>
    have ⟨m₁, eql₁, eqm₁, eqr₁⟩ := ih₁
    have ⟨m₂, eql₂, eqm₂, eqr₂⟩ := ih₂
    exact ⟨m₁ ++ m₂, by simp [eql₁, eql₂], by simp [←eqm₁, ←eqm₂], by simp [eqr₁, eqr₂]⟩
  | starEpsilon => exists []
  | starConcat _ _ ih₁ ih₂ =>
    have ⟨m₁, eql₁, eqm₁, eqr₁⟩ := ih₁
    have ⟨m₂, eql₂, eqm₂, eqr₂⟩ := ih₂
    exact ⟨m₁ ++ m₂, by simp [eql₁, eql₂], by simp [←eqm₁, ←eqm₂], by simp [eqr₁, eqr₂]⟩

end Regex.Data
