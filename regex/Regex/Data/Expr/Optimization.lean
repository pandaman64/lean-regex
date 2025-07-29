import Regex.Data.Expr.Basic

open Std

namespace Regex.Data.Expr

def nullOnly (expr : Expr) : Bool :=
  match expr with
  | .empty | .epsilon | .anchor _ => true
  | .char _ | .classes _ => false
  | .group _ e => e.nullOnly
  | .concat e₁ e₂ => e₁.nullOnly && e₂.nullOnly
  | .alternate e₁ e₂ => e₁.nullOnly && e₂.nullOnly
  | .star _ e => e.nullOnly

def firstChars (maxSize : Nat) (expr : Expr) : Option (HashSet Char) := do
  let cs ← match expr with
    | .empty | .epsilon | .anchor _ => .none
    | .char c => .some {c}
    | .classes _ => .none -- TODO: take .single class into account
    | .group _ e => e.firstChars maxSize
    | .concat e₁ e₂ => if e₁.nullOnly then e₂.firstChars maxSize else e₁.firstChars maxSize
    | .alternate e₁ e₂ => do
      let cs₁ ← e₁.firstChars maxSize
      let cs₂ ← e₂.firstChars maxSize
      return cs₁.union cs₂
    | .star _ => .none
  guard (cs.size ≤ maxSize)
  return cs

end Regex.Data.Expr
