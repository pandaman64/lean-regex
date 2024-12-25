import RegexCorrectness.Data.Expr.Semantics.Captures
import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Semantics.ProofData

set_option autoImplicit false

namespace Regex.NFA

inductive EquivUpdate : List (Nat × String.Pos × String.Pos) → List (Nat × String.Pos) → Prop where
  | empty : EquivUpdate [] []
  | group {groups updates tag first last} (h : EquivUpdate groups updates) :
    EquivUpdate ((tag, first, last) :: groups) ((2 * tag, first) :: updates ++ [(2 * tag + 1, last)])
  | concat {groups₁ groups₂ updates₁ updates₂} (h₁ : EquivUpdate groups₁ updates₁) (h₂ : EquivUpdate groups₂ updates₂) :
    EquivUpdate (groups₁ ++ groups₂) (updates₁ ++ updates₂)

end Regex.NFA
