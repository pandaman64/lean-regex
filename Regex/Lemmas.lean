import Std.Data.Nat.Lemmas

theorem Nat.eq_of_ge_of_lt {m n : Nat} (ge : m ≥ n) (lt : m < n + 1) : m = n := by
  have le : m ≤ n := Nat.le_of_lt_succ lt
  exact Nat.le_antisymm le ge
