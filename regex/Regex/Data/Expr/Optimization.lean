import Regex.Data.Expr.Basic

namespace Regex.Data.Expr

def nullOnly (expr : Expr) : Bool :=
  match expr with
  | .empty | .epsilon | .anchor _ => true
  | .char _ | .classes _ => false
  | .group _ e => e.nullOnly
  | .concat e₁ e₂ => e₁.nullOnly && e₂.nullOnly
  | .alternate e₁ e₂ => e₁.nullOnly && e₂.nullOnly
  | .star e => e.nullOnly

def firstChar (expr : Expr) : Option Char :=
  match expr with
  | .empty | .epsilon | .anchor _ => .none
  | .char c => .some c
  | .classes _ => .none
  | .group _ e => e.firstChar
  | .concat e₁ e₂ => if e₁.nullOnly then e₂.firstChar else e₁.firstChar
  | .alternate e₁ e₂ => do
    let c₁ ← e₁.firstChar
    let c₂ ← e₂.firstChar
    if c₁ = c₂ then .some c₁ else .none
  | .star _ => .none

end Regex.Data.Expr
