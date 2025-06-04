import Regex.Data.Nat

namespace BitVec

def set {w : Nat} (b : BitVec w) (i : Nat) : BitVec w :=
  if i < w then
    b ||| (1 <<< i)
  else
    b

@[simp]
theorem set_lt {w : Nat} (b : BitVec w) (i : Nat) (h : i < w) : b.set i = b ||| (1 <<< i) := by
  simp [set, h]

theorem getElem_set_eq {w : Nat} (b : BitVec w) (i : Nat) (h : i < w) : (b.set i)[i] := by
  simp [BitVec.ofNat, h]

theorem getElem_set_ne {w : Nat} (b : BitVec w) (i j : Nat) (h : i < w) (h' : j < w) (hne : i ≠ j) : (b.set i)[j] = b[j] := by
  simp only [set, h, ↓reduceIte, natCast_eq_ofNat, BitVec.ofNat, getElem_or, getElem_ofFin,
    Fin.val_ofNat', Nat.testBit_mod_two_pow, h', decide_true, Nat.testBit_shiftLeft, ge_iff_le,
    Bool.true_and, Bool.or_eq_left_iff_imp, Bool.and_eq_true, decide_eq_true_eq, and_imp]
  intro le test
  match h'' : j - i with
  | 0 => omega
  | n + 1 => simp [h'', Nat.testBit_succ] at test

def popcount {w : Nat} (b : BitVec w) : Nat := b.toNat.popcount

theorem popcount_set_not_getElem {w : Nat} (b : BitVec w) (i : Nat) (h : i < w) (h' : ¬b[i]) : popcount (b.set i) = popcount b + 1 := by
  conv =>
    lhs
    simp [popcount, h, Nat.popcount_or_one_shiftLeft, ←BitVec.getElem_eq_testBit_toNat, h']
  rfl

theorem popcount_le {w : Nat} (b : BitVec w) : popcount b ≤ w := Nat.popcount_le_of_lt_pow b.isLt

theorem sub_lt_popcount_set_not_getElem {w : Nat} (b : BitVec w) (i : Nat) (h : i < w) (h' : ¬b[i]) : w + 1 - popcount (b.set i) < w + 1 - popcount b := by
  have : popcount (b.set i) = popcount b + 1 := popcount_set_not_getElem b i h h'
  rw [this]
  have : popcount b ≤ w := popcount_le b
  omega

end BitVec
