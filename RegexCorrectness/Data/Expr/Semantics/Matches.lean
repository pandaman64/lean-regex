import Regex.Data.Expr

namespace Regex.Data

/--
A language accepted by a regular expression.
-/
inductive Expr.matches : List Char → Expr → Prop where
  | char (c : Char) : Expr.matches [c] (.char c)
  | sparse (cs : Classes) (c : Char) (h : c ∈ cs) : Expr.matches [c] (.classes cs)
  | epsilon : Expr.matches [] .epsilon
  | group (m : Expr.matches s r) : Expr.matches s (.group i r)
  | alternateLeft {cs : List Char} {r₁ r₂ : Expr} : Expr.matches cs r₁ → Expr.matches cs (.alternate r₁ r₂)
  | alternateRight {cs : List Char} {r₁ r₂ : Expr} : Expr.matches cs r₂ → Expr.matches cs (.alternate r₁ r₂)
  | concat (cs₁ cs₂ : List Char) (r₁ r₂ : Expr) :
    Expr.matches cs₁ r₁ → Expr.matches cs₂ r₂ → Expr.matches (cs₁ ++ cs₂) (.concat r₁ r₂)
  | starEpsilon : Expr.matches [] (.star r)
  | starConcat (cs₁ cs₂ : List Char) (r : Expr) :
    Expr.matches cs₁ r → Expr.matches cs₂ (.star r) → Expr.matches (cs₁ ++ cs₂) (.star r)

end Regex.Data
