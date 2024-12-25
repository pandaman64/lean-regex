import Regex.Data.Expr
import RegexCorrectness.Data.Span

set_option autoImplicit false

namespace Regex.Data

inductive Expr.Captures : Span → Span → List (Nat × String.Pos × String.Pos) → Expr → Prop where
  | char {l c r} : Expr.Captures ⟨l, [], c :: r⟩ ⟨l, [c], r⟩ [] (.char c)
  | sparse {l c r cs} (h : c ∈ cs) : Expr.Captures ⟨l, [], c :: r⟩ ⟨l, [c], r⟩ [] (.classes cs)
  | epsilon {l r} : Expr.Captures ⟨l, [], r⟩ ⟨l, [], r⟩ [] .epsilon
  | group {span span' groups tag e} (cap : Expr.Captures span span' groups e) :
    Expr.Captures span span' ((tag, span.curr, span'.curr) :: groups) (.group tag e)
  | alternateLeft {span span' groups e₁ e₂} (cap : Expr.Captures span span' groups e₁) :
    Expr.Captures span span' groups (.alternate e₁ e₂)
  | alternateRight {span span' groups e₁ e₂} (cap : Expr.Captures span span' groups e₂) :
    Expr.Captures span span' groups (.alternate e₁ e₂)
  | concat {span span' span'' groups₁ groups₂ e₁ e₂} (cap₁ : Expr.Captures span span' groups₁ e₁) (cap₂ : Expr.Captures span' span'' groups₂ e₂) :
    Expr.Captures span span'' (groups₁ ++ groups₂) (.concat e₁ e₂)
  | starEpsilon {l r e} : Expr.Captures ⟨l, [], r⟩ ⟨l, [], r⟩ [] (.star e)
  | starConcat {span span' span'' groups groups' e} (cap₁ : Expr.Captures span span' groups e) (cap₂ : Expr.Captures span' span'' groups' (.star e)) :
    Expr.Captures span span'' (groups ++ groups') (.star e)

end Regex.Data
