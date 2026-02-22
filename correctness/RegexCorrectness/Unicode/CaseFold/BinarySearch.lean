import Regex.Unicode.CaseFold

namespace Regex.Unicode

theorem binarySearch_spec {α} (c : Char) (values : Array α) (f : α → Char)
  (hsorted : ∀ i j : Fin values.size, i < j → f values[i] < f values[j])
  (lo hi : Nat)
  (le : hi ≤ values.size)
  (loInv : ∀ i : Fin values.size, i.val < lo → f values[i] < c)
  (hiInv : ∀ i : Fin values.size, hi ≤ i.val → c ≤ f values[i]) :
  ∀ i : Fin values.size, if i.val < binarySearch c values f lo hi le then f values[i] < c else c ≤ f values[i] := by
  fun_induction binarySearch c values f lo hi le
  next => grind
  next lo hi le₂ nge mid hmid eq =>
    intro i
    split
    next lt => grind [hsorted i ⟨mid, hmid⟩ lt]
    next nlt =>
      cases Nat.eq_or_lt_of_not_lt nlt with
      | inl eq' => grind
      | inr lt => grind [hsorted ⟨mid, hmid⟩ i lt]
  next lo hi le₂ nge mid hmid ne lt ih =>
    refine ih loInv ?_
    intro i le
    have : f values[mid] ≤ f values[i] := by
      cases Nat.eq_or_lt_of_le le with
      | inl eq => grind
      | inr lt => grind [hsorted ⟨mid, hmid⟩ i lt]
    grind
  next lo hi le₂ nge mid hmid ne nlt ih =>
    refine ih ?_ hiInv
    intro i lt
    have gt : f values[mid] < c := by grind
    cases Nat.lt_or_eq_of_le (by grind : i.val ≤ mid) with
    | inl lt => grind [hsorted i ⟨mid, hmid⟩ lt]
    | inr eq => grind

theorem le_binarySearch_of_lt {α} (c : Char) (values : Array α) (f : α → Char)
  (hsorted : ∀ i j : Fin values.size, i < j → f values[i] < f values[j])
  (lt : binarySearch c values f < values.size) :
  c ≤ f values[binarySearch c values f] := by
  have spec := binarySearch_spec c values f hsorted 0 values.size (by grind) (by grind) (by grind) ⟨binarySearch c values f, lt⟩
  grind

theorem binarySearch_of_mem {α} (c : Char) (values : Array α) (f : α → Char)
  (hsorted : ∀ i j : Fin values.size, i < j → f values[i] < f values[j])
  (i : Fin values.size) (h : f values[i] = c) :
  binarySearch c values f = i := by
  have spec := binarySearch_spec c values f hsorted 0 values.size (by grind) (by grind) (by grind) i
  split at spec
  next lt => grind
  next nlt =>
    cases Nat.eq_or_lt_of_not_lt nlt with
    | inl eq => grind
    | inr lt =>
      have lt' : c < f values[i] := Nat.lt_of_le_of_lt
        (le_binarySearch_of_lt c values f hsorted (by grind))
        (hsorted ⟨binarySearch c values f, by grind⟩ i lt)
      grind

end Regex.Unicode
