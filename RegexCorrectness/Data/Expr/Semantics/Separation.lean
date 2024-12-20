import Regex.Data.Expr
import Mathlib.Data.Finset.Basic

namespace Regex.Data.Expr

def tags : Expr → Finset Nat
| .empty | .epsilon | .char _ | .classes _ => ∅
| .group tag e => {tag} ∪ e.tags
| .alternate e₁ e₂ => e₁.tags ∪ e₂.tags
| .concat e₁ e₂ => e₁.tags ∪ e₂.tags
| .star e => e.tags

def Disjoint : Expr → Prop
| .empty | .epsilon | .char _ | .classes _ => True
| .group tag e => tag ∉ e.tags ∧ e.Disjoint
| .alternate e₁ e₂ => e₁.tags ∩ e₂.tags = ∅ ∧ e₁.Disjoint ∧ e₂.Disjoint
| .concat e₁ e₂ => e₁.tags ∩ e₂.tags = ∅ ∧ e₁.Disjoint ∧ e₂.Disjoint
| .star e => e.Disjoint

end Regex.Data.Expr
