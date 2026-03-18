module

public import RegexCorrectness.Data.Expr.Semantics.Captures

open String (Pos)

public section

namespace Regex.Data.Expr

@[expose, grind =]
def Nullable : Expr → Prop
  | .empty | .epsilon | .anchor _ => True
  | .char _ => False
  | .classes _ => False
  | .group _ e => e.Nullable
  | .concat e₁ e₂ => e₁.Nullable ∧ e₂.Nullable
  | .alternate e₁ e₂ => e₁.Nullable ∨ e₂.Nullable
  | .star _ _ => True

theorem Captures.lt_of_not_nullable {s} {p p' : Pos s} {groups e}
  (h : ¬Nullable e) (c : Expr.Captures p p' groups e) :
  p < p' := by
  induction c
  case concat c₁ c₂ _ _ => grind [c₁.le, c₂.le]
  all_goals grind [Pos.lt_next]

@[expose, grind =]
def NullableStar : Expr → Prop
  | .empty | .epsilon | .anchor _ | .char _ | .classes _ => False
  | .group _ e => e.NullableStar
  | .concat e₁ e₂ => e₁.NullableStar ∨ e₂.NullableStar
  | .alternate e₁ e₂ => e₁.NullableStar ∨ e₂.NullableStar
  | .star _ e => e.Nullable ∨ e.NullableStar

end Regex.Data.Expr

end
