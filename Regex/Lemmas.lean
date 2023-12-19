import Mathlib.Tactic.Common
import Mathlib.Init.Order.Defs

theorem le_foldl_of_le [Preorder α] {f₁ f₂ : α → β → α} {a₁ a₂ : α}
  (lef : ∀a₁ a₂ b, a₁ ≤ a₂ → f₁ a₁ b ≤ f₂ a₂ b) (le: a₁ ≤ a₂) (l : List β) :
  List.foldl f₁ a₁ l ≤ List.foldl f₂ a₂ l := by
  induction l generalizing a₁ a₂ with
  | nil => assumption
  | cons x _ ih => exact ih (lef a₁ a₂ x le)

theorem String.eq_of_append_of_eq_of_append {s s₁ s₂ : String} (h : s = s₁ ++ s₂) :
  s.data = s₁.data ++ s₂.data := by
  subst h
  simp only [data_append]
