import Batteries.Data.Array

theorem Array.zero_lt_size_of_not_empty {a : Array α} (hemp : ¬ a.isEmpty) :
  0 < a.size := by
  apply Nat.zero_lt_of_ne_zero
  intro heq
  have : a = #[] := eq_empty_of_size_eq_zero heq
  simp [this] at hemp

def Array.back' (a : Array α) (hemp : ¬ a.isEmpty) : α :=
  have : 0 < a.size := zero_lt_size_of_not_empty hemp
  a[a.size - 1]

theorem Array.lt_size_of_pop_of_not_empty (a : Array α) (hemp : ¬ a.isEmpty) :
  (a.pop).size < a.size := by
  have : 0 < a.size := zero_lt_size_of_not_empty hemp
  have : a.size - 1 < a.size := Nat.sub_lt_of_pos_le (by decide) this
  simp [Array.pop]
  exact this
