import RegexCorrectness.Data.Expr.Semantics

set_option autoImplicit false

open Regex.Data (CaptureGroups)

namespace Regex.NFA

inductive EquivUpdate : CaptureGroups → List (Nat × String.Pos) → Prop where
  | empty : EquivUpdate .empty []
  | group {groups updates tag first last} (h : EquivUpdate groups updates) :
    EquivUpdate (.group tag first last groups) ((2 * tag, first) :: updates ++ [(2 * tag + 1, last)])
  | concat {groups₁ groups₂ updates₁ updates₂} (h₁ : EquivUpdate groups₁ updates₁) (h₂ : EquivUpdate groups₂ updates₂) :
    EquivUpdate (.concat groups₁ groups₂) (updates₁ ++ updates₂)

end Regex.NFA
