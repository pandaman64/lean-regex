import Regex.Data.Expr
import RegexCorrectness.Data.Expr.Semantics.CaptureGroups
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (ValidPos)

namespace Regex.Data

inductive Expr.Captures {s : String} : ValidPos s → ValidPos s → CaptureGroups s→ Expr → Prop where
  | char {p c} (ne : p ≠ s.endValidPos) (eq : p.get ne = c) : Expr.Captures p (p.next ne) .empty (.char c)
  | sparse {p cs} (ne : p ≠ s.endValidPos) (h : p.get ne ∈ cs) : Expr.Captures p (p.next ne) .empty (.classes cs)
  | epsilon {p} : Expr.Captures p p .empty .epsilon
  | anchor {p anchor} (h : anchor.test p) : Expr.Captures p p .empty (.anchor anchor)
  | group {p p' groups tag e} (cap : Expr.Captures p p' groups e) :
    Expr.Captures p p' (.group tag p p' groups) (.group tag e)
  | alternateLeft {p p' groups e₁ e₂} (cap : Expr.Captures p p' groups e₁) :
    Expr.Captures p p' groups (.alternate e₁ e₂)
  | alternateRight {p p' groups e₁ e₂} (cap : Expr.Captures p p' groups e₂) :
    Expr.Captures p p' groups (.alternate e₁ e₂)
  | concat {p p' p'' groups₁ groups₂ e₁ e₂} (cap₁ : Expr.Captures p p' groups₁ e₁) (cap₂ : Expr.Captures p' p'' groups₂ e₂) :
    Expr.Captures p p'' (.concat groups₁ groups₂) (.concat e₁ e₂)
  | starEpsilon {p greedy e} : Expr.Captures p p .empty (.star greedy e)
  | starConcat {p p' p'' groups₁ groups₂ greedy e} (cap₁ : Expr.Captures p p' groups₁ e) (cap₂ : Expr.Captures p' p'' groups₂ (.star greedy e)) :
    Expr.Captures p p'' (.concat groups₁ groups₂) (.star greedy e)

namespace Expr.Captures

theorem le {s} {p p' : ValidPos s} {groups e} (c : Expr.Captures p p' groups e) : p ≤ p' := by
  induction c with
  | char vf => exact ValidPos.le_of_lt (ValidPos.lt_next _)
  | sparse vf => exact ValidPos.le_of_lt (ValidPos.lt_next _)
  | epsilon => exact Nat.le_refl _
  | anchor => exact Nat.le_refl _
  | group _ ih => exact ih
  | alternateLeft _ ih => exact ih
  | alternateRight _ ih => exact ih
  | concat _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂
  | starEpsilon => exact Nat.le_refl _
  | starConcat _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

end Expr.Captures

end Regex.Data
