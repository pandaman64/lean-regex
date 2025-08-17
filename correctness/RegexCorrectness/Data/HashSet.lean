import Std.Data.HashSet

universe u

variable {α : Type u} [BEq α] [Hashable α]

namespace Std.HashSet

theorem mem_union_iff {a : α} (m₁ m₂ : HashSet α) :
    a ∈ m₁.union m₂ ↔ a ∈ m₁ ∨ a ∈ m₂ := sorry

theorem contains_toArray_iff {a : α} (m : HashSet α) :
    m.contains a ↔ m.toArray.contains a := sorry

end Std.HashSet
