import Std.Data.HashSet

universe u

variable {α : Type u} [BEq α] [Hashable α] [EquivBEq α] [LawfulHashable α]

namespace Std.HashSet

theorem mem_union_iff {a : α} (m₁ m₂ : HashSet α) :
    a ∈ m₁.union m₂ ↔ a ∈ m₁ ∨ a ∈ m₂ := by
    simp [union, fold_eq_foldl_toList]
    rw [mem_iff_contains (m:= m₂), ← contains_toList]
    generalize m₂.toList = l
    induction l generalizing m₁ with
    | nil => simp
    | cons hd tl ih =>
      simp [ih]
      rw [BEq.comm]
      grind

theorem contains_toArray_iff {a : α} (m : HashSet α) :
    m.contains a ↔ m.toArray.contains a := sorry

end Std.HashSet
