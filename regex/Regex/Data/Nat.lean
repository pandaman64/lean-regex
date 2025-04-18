namespace Nat

def popcount (n : Nat) : Nat :=
  if n = 0 then
    0
  else
    popcount (n / 2) + n % 2

@[simp]
theorem popcount_zero : popcount 0 = 0 := by
  conv =>
    lhs
    unfold popcount
    simp

theorem popcount_ne {n : Nat} (h : n ≠ 0) : popcount n = popcount (n / 2) + n % 2 := by
  conv =>
    lhs
    unfold popcount
    simp [h]

theorem popcount_odd {n : Nat} (h : n.testBit 0) : popcount n = popcount (n / 2) + 1 := by
  conv =>
    lhs
    unfold popcount
  split
  next h' => simp [h'] at h
  next h' => simp only [Nat.add_left_cancel_iff, mod_two_eq_one_iff_testBit_zero, h]

theorem popcount_even {n : Nat} (h : ¬n.testBit 0) : popcount n = popcount (n / 2) := by
  conv =>
    lhs
    unfold popcount
  split
  next h' => simp [h']
  next h' => simp only [Nat.add_right_eq_self, mod_two_eq_zero_iff_testBit_zero, h]

theorem popcount_le_of_lt_pow {n w : Nat} (h : n < 2 ^ w) : popcount n ≤ w := by
  induction n using popcount.induct generalizing w with
  | case1 => simp
  | case2 n ne ih =>
    match w with
    | 0 => simp [ne] at h
    | w + 1 =>
      simp [popcount_ne ne]
      apply Nat.add_le_add (ih (w := w) (Nat.div_lt_of_lt_mul (by omega))) (by omega)

theorem one_shiftLeft_lt_pow {n w : Nat} (h : n < w) : 1 <<< n < 2 ^ w := by
  rw [one_shiftLeft]
  exact Nat.pow_lt_pow_of_lt (by omega) h

@[simp]
theorem one_shiftLeft_mod_two_pow {n w : Nat} (h : n < w) : (1 <<< n) % (2 ^ w) = 1 <<< n :=
  mod_eq_of_lt (one_shiftLeft_lt_pow h)

theorem zero_of_or_zero {n m : Nat} (h : n ||| m = 0) : n = 0 ∧ m = 0 := by
  have : ∀ i, (n ||| m).testBit i = false := h ▸ zero_testBit
  simp at this
  exact ⟨eq_of_testBit_eq fun i => by rw [(this i).1, zero_testBit], eq_of_testBit_eq fun i => by rw [(this i).2, zero_testBit]⟩

theorem or_ne_zero {n m : Nat} (h : m ≠ 0) : n ||| m ≠ 0 := by
  refine Decidable.by_contra fun h' => ?_
  rw [Decidable.not_not] at h'
  exact h (zero_of_or_zero h').2

theorem or_one_shiftLeft_ne_zero {n : Nat} : (n ||| 1 <<< i) ≠ 0 := by
  have : 1 <<< i ≠ 0 := by
    rw [one_shiftLeft]
    exact Nat.ne_zero_of_lt (Nat.two_pow_pos i)
  exact or_ne_zero this

theorem or_one_mod_two {n : Nat} : (n ||| 1) % 2 = 1 := by
  simp [Nat.or_mod_two_eq_one]

theorem one_shiftLeft_succ_div_two : (1 <<< (i + 1)) / 2 = 1 <<< i := by
  simp [one_shiftLeft]
  omega

theorem or_one_shiftLeft_succ_mod_two {n : Nat} : (n ||| 1 <<< (i + 1)) % 2 = n % 2 := by
  rw [one_shiftLeft]
  match h : n % 2 with
  | 0 => simp [mod_two_eq_zero_iff_testBit_zero, h]
  | 1 =>
    rw [mod_two_eq_one_iff_testBit_zero]
    simp [h]
  | n + 2 => omega

theorem ne_zero_of_testBit {n i : Nat} (h : n.testBit i) : n ≠ 0 := by
  intro h'
  have := (h' ▸ zero_testBit) i
  simpa [h]

theorem popcount_or_one_shiftLeft (n i : Nat) : popcount (n ||| (1 <<< i)) = if n.testBit i then popcount n else popcount n + 1 := by
  induction i generalizing n with
  | zero =>
    split
    next h => simp [popcount_ne, or_ne_zero, or_one_mod_two, or_div_two, popcount_odd h]
    next h => simp [popcount_ne, or_ne_zero, or_one_mod_two, or_div_two, popcount_even h]
  | succ i ih =>
    simp [popcount_ne, or_one_shiftLeft_ne_zero, or_div_two, or_one_shiftLeft_succ_mod_two]
    rw [one_shiftLeft_succ_div_two, ih (n / 2), ←testBit_succ]
    if h' : n.testBit (i + 1) then
      simp [h']
      have : n ≠ 0 := ne_zero_of_testBit h'
      exact (popcount_ne this).symm
    else
      simp [h']
      if h'' : n = 0 then
        simp [h'']
      else
        simp [popcount_ne h'']
        omega

end Nat
