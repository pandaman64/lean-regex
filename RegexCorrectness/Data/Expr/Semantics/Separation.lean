import Regex.Data.Expr
import Mathlib.Data.Finset.Basic
import RegexCorrectness.Data.Expr.Semantics.Captures

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

theorem Captures.mem_tags_of_mem_update {e : Expr} {span span' update} (c : e.Captures span span' update) :
  ∀ tag first last, (tag, first, last) ∈ update → tag ∈ e.tags := by
  intro tag first last mem
  induction c with
  | char => simp at mem
  | sparse => simp at mem
  | epsilon => simp at mem
  | group _ ih =>
    simp at mem
    cases mem with
    | inl mem => simp [tags, ih mem]
    | inr eq => simp [eq, tags]
  | alternateLeft _ ih => simp [tags, ih mem]
  | alternateRight _ ih => simp [tags, ih mem]
  | concat _ _ ih₁ ih₂ =>
    simp only [List.mem_append] at mem
    cases mem with
    | inl mem₁ => simp [tags, ih₁ mem₁]
    | inr mem₂ => simp [tags, ih₂ mem₂]
  | starEpsilon => simp at mem
  | starConcat _ _ ih₁ ih₂ =>
    simp only [List.mem_append] at mem
    cases mem with
    | inl mem₁ => simp [tags, ih₁ mem₁]
    | inr mem₂ => exact ih₂ mem₂

end Regex.Data.Expr
