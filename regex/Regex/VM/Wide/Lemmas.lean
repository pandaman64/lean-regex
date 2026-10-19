module

public import Regex.VM.Wide.Basic

/-!
Properties of the little-endian byte buffers.

`setList` and `pushList` are the single induction. `UInt32` and `UInt64`
stores are those lists, so the read-back and disjointness lemmas do not repeat
per byte.
-/

public section

namespace Regex.VM.Wide

/-- `2^32` fits in `USize` on every platform Lean supports (`numBits` is 32 or 64). -/
theorem two_pow_32_le_usize : 2 ^ 32 ≤ USize.size := by
  rw [USize.size_eq_two_pow]
  exact Nat.pow_le_pow_right (by decide) System.Platform.le_numBits

/-- A natural below `2^32` is still below `2^numBits`. -/
theorem lt_two_pow_numBits_of_lt_2_pow_32 {n : Nat} (h : n < 2 ^ 32) :
    n < 2 ^ System.Platform.numBits := by
  rw [← USize.size_eq_two_pow]
  exact Nat.lt_of_lt_of_le h two_pow_32_le_usize

/-- A natural below `2^32` survives the round trip through `USize`. -/
theorem toNat_toUSize_of_lt_2_pow_32 {n : Nat} (h : n < 2 ^ 32) : n.toUSize.toNat = n := by
  rw [Nat.toUSize, USize.toNat_ofNat']
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

theorem toNat_uSize_ofNat_of_lt (n : Nat) (h : n < 2 ^ 32) : (OfNat.ofNat n : USize).toNat = n := by
  rw [USize.toNat_ofNat]
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

/-- Addition of two `USize`s below `2^32` does not wrap. -/
theorem toNat_add_of_lt_2_pow_32 {a b : USize} (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

/-- Multiplication of two `USize`s below `2^32` does not wrap. -/
theorem toNat_mul_of_lt_2_pow_32 {a b : USize} (h : a.toNat * b.toNat < 2 ^ 32) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [USize.toNat_mul]
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

/-- Adding a `Nat` literal below `2^32` does not wrap. -/
theorem toNat_add_nat_of_lt_2_pow_32 (off : USize) (k : Nat) (hk : k < 2 ^ 32)
    (h : off.toNat + k < 2 ^ 32) :
    (off + OfNat.ofNat k).toNat = off.toNat + k := by
  rw [USize.toNat_add, toNat_uSize_ofNat_of_lt k hk]
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

/-- `a + 1` does not wrap when the successor is still below `2^32`. -/
theorem toNat_u32_add_one {a : UInt32} (h : a.toNat + 1 < 2 ^ 32) :
    (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add, UInt32.toNat_one]
  exact Nat.mod_eq_of_lt h

/-- `i < n` forces `i + 1` to stay inside `UInt32`. -/
theorem toNat_u32_add_one_of_lt {i n : UInt32} (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  apply toNat_u32_add_one
  have hlt : i.toNat < n.toNat := (UInt32.lt_iff_toNat_lt).mp h
  have := UInt32.toNat_lt n
  omega

/-- `i.toUSize * k` does not wrap when the product is below `2^32`. -/
theorem toNat_u32_mul_ofNat (i : UInt32) (k : Nat) (hk : k < 2 ^ 32) (h : i.toNat * k < 2 ^ 32) :
    (i.toUSize * OfNat.ofNat k).toNat = i.toNat * k := by
  rw [toNat_mul_of_lt_2_pow_32 (by
      rw [UInt32.toNat_toUSize, toNat_uSize_ofNat_of_lt k hk]
      exact h),
    UInt32.toNat_toUSize, toNat_uSize_ofNat_of_lt k hk]

end Regex.VM.Wide

namespace ByteArray

private theorem get_set_self (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h)[i]'(by rw [ByteArray.size_set]; exact h) = v := by
  simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_set, Array.getElem_set_self]

private theorem get_set_ne (a : ByteArray) (i j : Nat) (v : UInt8)
    (hi : i < a.size) (hj : j < a.size) (hne : i ≠ j) :
    (a.set i v hi)[j]'(by rw [ByteArray.size_set]; exact hj) = a[j] := by
  simp only [ByteArray.getElem_eq_getElem_data, ByteArray.data_set]
  exact Array.getElem_set_ne (by simpa [← ByteArray.size_data] using hi)
    (by simpa [← ByteArray.size_data] using hj) hne

private theorem get_irrel (a : ByteArray) (i : Nat) (h1 h2 : i < a.size) :
    a[i]'h1 = a[i]'h2 := rfl

/-- Reading at propositionally equal indices agrees. -/
private theorem get_idx {a : ByteArray} {i j : Nat} (hij : i = j) (hi : i < a.size) :
    a[i]'hi = a[j]'(hij ▸ hi) := by
  subst hij
  rfl

@[simp]
theorem setList_size (a : ByteArray) (off : Nat) (bytes : List UInt8)
    (h : off + bytes.length ≤ a.size) :
    (a.setList off bytes h).size = a.size := by
  induction bytes generalizing a off with
  | nil => simp [setList]
  | cons b bs ih =>
    unfold setList
    rw [ih, ByteArray.size_set]

/-- A byte outside the written interval is unchanged. -/
theorem setList_get_out (a : ByteArray) (off : Nat) (bytes : List UInt8)
    (h : off + bytes.length ≤ a.size) (j : Nat) (hj : j < a.size)
    (hout : j < off ∨ off + bytes.length ≤ j) :
    (a.setList off bytes h)[j]'(by rw [setList_size]; exact hj) = a[j] := by
  induction bytes generalizing a off with
  | nil => simp [setList]
  | cons b bs ih =>
    have hlen : off + (bs.length + 1) ≤ a.size := by simpa [List.length_cons] using h
    have hoff : off < a.size := by omega
    unfold setList
    have hj' : j < (a.set off b hoff).size := by rw [ByteArray.size_set]; exact hj
    have hout' : j < off + 1 ∨ (off + 1) + bs.length ≤ j := by
      cases hout with
      | inl hlt => exact Or.inl (Nat.lt_trans hlt (Nat.lt_succ_self _))
      | inr hge =>
        right
        simp only [List.length_cons] at hge
        omega
    have hne : off ≠ j := by
      cases hout with
      | inl hlt => omega
      | inr hge =>
        simp only [List.length_cons] at hge
        omega
    have htail : (off + 1) + bs.length ≤ (a.set off b hoff).size := by
      rw [ByteArray.size_set]
      omega
    exact (ih (a.set off b hoff) (off + 1) htail hj' hout').trans
      (get_set_ne a off j b hoff hj hne)

/-- Byte `off + k` reads back as `bytes[k]`. -/
theorem setList_get (a : ByteArray) (off : Nat) (bytes : List UInt8)
    (h : off + bytes.length ≤ a.size) (k : Nat) (hk : k < bytes.length) :
    (a.setList off bytes h)[off + k]'(by rw [setList_size]; omega) = bytes[k] := by
  induction bytes generalizing a off k with
  | nil => simp at hk
  | cons b bs ih =>
    have hlen : off + (bs.length + 1) ≤ a.size := by simpa [List.length_cons] using h
    have hoff : off < a.size := by omega
    unfold setList
    have htail : (off + 1) + bs.length ≤ (a.set off b hoff).size := by
      rw [ByteArray.size_set]
      omega
    cases k with
    | zero =>
      have hsz : off < (a.set off b hoff).size := by rw [ByteArray.size_set]; omega
      have hkeep := setList_get_out (a.set off b hoff) (off + 1) bs htail off hsz
        (Or.inl (Nat.lt_succ_self _))
      simp only [List.getElem_cons_zero]
      exact hkeep.trans (get_set_self a off b hoff)
    | succ k =>
      have hk' : k < bs.length := by simp at hk; omega
      have hrec := ih (a.set off b hoff) (off + 1) htail k hk'
      simp only [List.getElem_cons_succ]
      have heq : (off + 1) + k = off + (k + 1) := by omega
      exact (get_idx heq _).symm.trans hrec

@[simp]
theorem pushList_size (a : ByteArray) (bs : List UInt8) :
    (a.pushList bs).size = a.size + bs.length := by
  induction bs generalizing a with
  | nil => simp [pushList]
  | cons b bs ih =>
    unfold pushList
    rw [ih, ByteArray.size_push, List.length_cons]
    omega

theorem pushList_get_lt (a : ByteArray) (bs : List UInt8) (i : Nat) (hi : i < a.size) :
    (a.pushList bs)[i]'(by rw [pushList_size]; omega) = a[i] := by
  induction bs generalizing a with
  | nil => simp [pushList]
  | cons b bs ih =>
    unfold pushList
    have h1 : i < (a.push b).size := by rw [ByteArray.size_push]; omega
    exact (ih (a.push b) h1).trans (by
      simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push,
        Array.getElem_push_lt (by simpa [← ByteArray.size_data] using hi)])

theorem pushList_get (a : ByteArray) (bs : List UInt8) (k : Nat) (hk : k < bs.length) :
    (a.pushList bs)[a.size + k]'(by rw [pushList_size]; omega) = bs[k] := by
  induction bs generalizing a k with
  | nil => simp at hk
  | cons b bs ih =>
    unfold pushList
    cases k with
    | zero =>
      have hlt : a.size < (a.push b).size := by rw [ByteArray.size_push]; omega
      have htail := pushList_get_lt (a.push b) bs a.size hlt
      simp only [List.getElem_cons_zero]
      exact htail.trans (by
        simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, ← ByteArray.size_data,
          Array.getElem_push_eq])
    | succ k =>
      have hk' : k < bs.length := by simp at hk; omega
      have hrec := ih (a.push b) k hk'
      simp only [List.getElem_cons_succ]
      have heq : (a.push b).size + k = a.size + (k + 1) := by
        rw [ByteArray.size_push]
        omega
      exact (get_idx heq _).symm.trans hrec

private theorem zeroLoop_size (n : Nat) (a : ByteArray) : (zeroLoop n a).size = a.size + n := by
  induction n generalizing a with
  | zero => simp [zeroLoop]
  | succ n ih =>
    unfold zeroLoop
    rw [ih, ByteArray.size_push]
    omega

@[simp]
theorem zero_size (n : USize) : (zero n).size = n.toNat := by
  rw [zero_eq, zeroLoop_size]
  simp

private theorem zeroLoop_get (n : Nat) (a : ByteArray)
    (ha : ∀ j, (hj : j < a.size) → a[j] = 0) (i : Nat) (hi : i < (zeroLoop n a).size) :
    (zeroLoop n a)[i] = 0 := by
  induction n generalizing a i with
  | zero =>
    simp only [zeroLoop] at hi ⊢
    exact ha i hi
  | succ n ih =>
    unfold zeroLoop at hi ⊢
    refine ih (a.push 0) (fun j hj => ?_) i hi
    by_cases hlt : j < a.size
    · have hpush : (a.push 0)[j] = a[j] := by
        simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push,
          Array.getElem_push_lt (by simpa [← ByteArray.size_data] using hlt)]
      exact hpush.trans (ha j hlt)
    · have hj' : j = a.size := by
        rw [ByteArray.size_push] at hj
        omega
      simp [hj', ByteArray.getElem_eq_getElem_data, ByteArray.data_push, ← ByteArray.size_data,
        Array.getElem_push_eq]

private theorem zero_get (n : USize) (i : Nat) (hi : i < (zero n).size) : (zero n)[i] = 0 := by
  unfold zero at hi ⊢
  rw [zeroLoop_size, ByteArray.size_empty] at hi
  exact zeroLoop_get n.toNat .empty (fun j hj => by simp at hj) i (by
    rwa [zeroLoop_size, ByteArray.size_empty])

/-- Every wide load from a zero block is zero. -/
theorem ugetUInt64LE_zero (n off : USize) (h : off.toNat + 8 ≤ (zero n).size) :
    (zero n).ugetUInt64LE off h = 0 := by
  unfold ugetUInt64LE
  have b (k : Nat) (hk : k < 8) :
      (zero n)[off.toNat + k]'(by omega) = 0 :=
    zero_get n (off.toNat + k) (by omega)
  have b0 : (zero n)[off.toNat]'(by omega) = 0 := by simpa using b 0 (by decide)
  simp [b0, b 1 (by decide), b 2 (by decide), b 3 (by decide),
    b 4 (by decide), b 5 (by decide), b 6 (by decide), b 7 (by decide)]

theorem usetUInt32LE_size (a : ByteArray) (off : USize) (v : UInt32) (h : off.toNat + 4 ≤ a.size) :
    (a.usetUInt32LE off v h).size = a.size := by
  unfold usetUInt32LE
  simp [u32Bytes]

theorem usetUInt64LE_size (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) :
    (a.usetUInt64LE off v h).size = a.size := by
  unfold usetUInt64LE
  simp [u64Bytes]

end ByteArray

namespace Regex.VM.Wide

open ByteArray (setList_get setList_get_out)

private theorem orLow (low high i : Nat) (hlt : low < 2 ^ i) :
    low ||| (high <<< i) = low + high * 2 ^ i := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm high (2 ^ i), Nat.or_comm]
  exact Nat.add_comm _ _ ▸ (Nat.two_pow_add_eq_or_of_lt hlt high).symm

private theorem mod_mul_eq (n a b : Nat) (ha : 0 < a) (hb : 0 < b) :
    n % (a * b) = n % a + (n / a % b) * a := by
  have hdiv : a * (n / a) + n % a = n := Nat.div_add_mod n a
  have hq : b * ((n / a) / b) + (n / a) % b = n / a := Nat.div_add_mod (n / a) b
  have hreplace : a * (n / a) + n % a =
      a * (b * ((n / a) / b) + (n / a) % b) + n % a := by
    conv =>
      lhs
      arg 1
      arg 2
      rw [← hq]
  have hexpand : n = (a * b) * ((n / a) / b) + (a * ((n / a) % b) + n % a) := by
    calc
      n = a * (n / a) + n % a := hdiv.symm
      _ = a * (b * ((n / a) / b) + (n / a) % b) + n % a := hreplace
      _ = a * (b * ((n / a) / b)) + a * ((n / a) % b) + n % a := by rw [Nat.mul_add]
      _ = (a * b) * ((n / a) / b) + a * ((n / a) % b) + n % a := by rw [← Nat.mul_assoc]
      _ = (a * b) * ((n / a) / b) + (a * ((n / a) % b) + n % a) := by rw [Nat.add_assoc]
  have hr1 : n % a < a := Nat.mod_lt _ ha
  have hr2 : (n / a) % b < b := Nat.mod_lt _ hb
  have hlt : a * ((n / a) % b) + n % a < a * b := by
    have hstep : a * ((n / a) % b) + n % a < a * ((n / a) % b) + a := Nat.add_lt_add_left hr1 _
    have hmul : a * ((n / a) % b) + a = a * (((n / a) % b) + 1) := by
      rw [Nat.mul_add, Nat.mul_one]
    have hle : ((n / a) % b) + 1 ≤ b := hr2
    rw [hmul] at hstep
    exact Nat.lt_of_lt_of_le hstep (Nat.mul_le_mul_left a hle)
  calc
    n % (a * b) = ((a * b) * ((n / a) / b) + (a * ((n / a) % b) + n % a)) % (a * b) := by
      rw [← hexpand]
    _ = (a * ((n / a) % b) + n % a) % (a * b) := by rw [Nat.mul_add_mod_self_left]
    _ = a * ((n / a) % b) + n % a := Nat.mod_eq_of_lt hlt
    _ = n % a + ((n / a) % b) * a := by rw [Nat.add_comm, Nat.mul_comm]

/-- Reassemble `k` little-endian bytes of `n`. -/
private def packBytes (n k : Nat) : Nat :=
  match k with
  | 0 => 0
  | k + 1 => packBytes n k ||| ((n >>> (8 * k)) % 256) <<< (8 * k)

private theorem packBytes_mod (n k : Nat) : packBytes n k = n % 2 ^ (8 * k) := by
  induction k with
  | zero =>
    simp [packBytes, Nat.pow_zero, Nat.mod_one]
  | succ k ih =>
    have e8k : 2 ^ (8 * (k + 1)) = 2 ^ (8 * k) * 256 := by
      rw [Nat.mul_succ, Nat.pow_add, show (2 : Nat) ^ 8 = 256 by decide]
    have low_lt : n % 2 ^ (8 * k) < 2 ^ (8 * k) := Nat.mod_lt _ (Nat.two_pow_pos _)
    rw [packBytes, ih, Nat.shiftRight_eq_div_pow]
    rw [orLow (n % 2 ^ (8 * k)) ((n / 2 ^ (8 * k)) % 256) (8 * k) low_lt]
    have hdecomp := mod_mul_eq n (2 ^ (8 * k)) 256 (Nat.two_pow_pos _) (by decide)
    rw [← e8k] at hdecomp
    exact hdecomp.symm

/-- A byte shifted by at most `w - 8` bits still fits in `w` bits. -/
private theorem byteShift_mod (w k b : Nat) (hk : k + 8 ≤ w) (hb : b < 256) :
    (b <<< k) % 2 ^ w = b <<< k := by
  apply Nat.mod_eq_of_lt
  rw [Nat.shiftLeft_eq]
  have hb' : b ≤ 255 := Nat.lt_succ_iff.mp hb
  have hk' : k ≤ w - 8 := by omega
  have hmul : b * 2 ^ k ≤ 255 * 2 ^ (w - 8) :=
    Nat.mul_le_mul hb' (Nat.pow_le_pow_right (by decide) hk')
  have h255 : 255 * 2 ^ (w - 8) < 2 ^ w := by
    have hbyte : 255 < 2 ^ 8 := by decide
    calc
      255 * 2 ^ (w - 8) < 2 ^ 8 * 2 ^ (w - 8) := Nat.mul_lt_mul_of_pos_right hbyte (Nat.two_pow_pos _)
      _ = 2 ^ (8 + (w - 8)) := by rw [← Nat.pow_add]
      _ = 2 ^ w := by
        have : 8 + (w - 8) = w := by omega
        rw [this]
  omega

private theorem le_nat (n w : Nat) (hn : n < 2 ^ w) (hw : w = 8 * (w / 8)) :
    packBytes n (w / 8) = n := by
  rw [packBytes_mod, ← hw]
  exact Nat.mod_eq_of_lt hn

/-- Four little-endian bytes reassemble the original `UInt32`. -/
private theorem u32_of_le_bytes (v : UInt32) :
    v.toUInt8.toUInt32 |||
      ((v >>> 8).toUInt8.toUInt32 <<< 8) |||
      ((v >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  apply UInt32.toNat_inj.mp
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight,
    UInt32.toNat_toUInt8, UInt8.toNat_toUInt32,
    show (8 : UInt32).toNat = 8 by decide, show (16 : UInt32).toNat = 16 by decide,
    show (24 : UInt32).toNat = 24 by decide,
    show 8 % 32 = 8 by decide, show 16 % 32 = 16 by decide, show 24 % 32 = 24 by decide]
  have hb (k : Nat) : v.toNat >>> k % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [byteShift_mod 32 8 _ (by decide) (hb 8),
    byteShift_mod 32 16 _ (by decide) (hb 16),
    byteShift_mod 32 24 _ (by decide) (hb 24)]
  have hpack : packBytes v.toNat 4 =
      v.toNat % 256 ||| (v.toNat >>> 8 % 256) <<< 8 ||| (v.toNat >>> 16 % 256) <<< 16 |||
        (v.toNat >>> 24 % 256) <<< 24 := by
    simp [packBytes, Nat.shiftLeft_zero, Nat.shiftRight_zero, Nat.zero_or]
  rw [← hpack]
  exact le_nat v.toNat 32 (UInt32.toNat_lt v) (by decide)

/-- Eight little-endian bytes reassemble the original `UInt64`. -/
private theorem u64_of_le_bytes (v : UInt64) :
    v.toUInt8.toUInt64 |||
      ((v >>> 8).toUInt8.toUInt64 <<< 8) |||
      ((v >>> 16).toUInt8.toUInt64 <<< 16) |||
      ((v >>> 24).toUInt8.toUInt64 <<< 24) |||
      ((v >>> 32).toUInt8.toUInt64 <<< 32) |||
      ((v >>> 40).toUInt8.toUInt64 <<< 40) |||
      ((v >>> 48).toUInt8.toUInt64 <<< 48) |||
      ((v >>> 56).toUInt8.toUInt64 <<< 56) = v := by
  apply UInt64.toNat_inj.mp
  simp only [UInt64.toNat_or, UInt64.toNat_shiftLeft, UInt64.toNat_shiftRight,
    UInt64.toNat_toUInt8, UInt8.toNat_toUInt64,
    show (8 : UInt64).toNat = 8 by decide, show (16 : UInt64).toNat = 16 by decide,
    show (24 : UInt64).toNat = 24 by decide, show (32 : UInt64).toNat = 32 by decide,
    show (40 : UInt64).toNat = 40 by decide, show (48 : UInt64).toNat = 48 by decide,
    show (56 : UInt64).toNat = 56 by decide,
    show 8 % 64 = 8 by decide, show 16 % 64 = 16 by decide, show 24 % 64 = 24 by decide,
    show 32 % 64 = 32 by decide, show 40 % 64 = 40 by decide, show 48 % 64 = 48 by decide,
    show 56 % 64 = 56 by decide]
  have hb (k : Nat) : v.toNat >>> k % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [byteShift_mod 64 8 _ (by decide) (hb 8), byteShift_mod 64 16 _ (by decide) (hb 16),
    byteShift_mod 64 24 _ (by decide) (hb 24), byteShift_mod 64 32 _ (by decide) (hb 32),
    byteShift_mod 64 40 _ (by decide) (hb 40), byteShift_mod 64 48 _ (by decide) (hb 48),
    byteShift_mod 64 56 _ (by decide) (hb 56)]
  have hpack : packBytes v.toNat 8 =
      v.toNat % 256 ||| (v.toNat >>> 8 % 256) <<< 8 ||| (v.toNat >>> 16 % 256) <<< 16 |||
        (v.toNat >>> 24 % 256) <<< 24 ||| (v.toNat >>> 32 % 256) <<< 32 |||
        (v.toNat >>> 40 % 256) <<< 40 ||| (v.toNat >>> 48 % 256) <<< 48 |||
        (v.toNat >>> 56 % 256) <<< 56 := by
    simp [packBytes, Nat.shiftLeft_zero, Nat.shiftRight_zero, Nat.zero_or]
  rw [← hpack]
  exact le_nat v.toNat 64 (UInt64.toNat_lt v) (by decide)

end Regex.VM.Wide

namespace ByteArray

/-- A buffer whose four bytes are `u32Bytes v` loads as `v`. -/
private theorem ugetUInt32LE_of_bytes (a : ByteArray) (off : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.size)
    (hb : ∀ k, (hk : k < 4) →
      a[off.toNat + k]'(by omega) = (u32Bytes v)[k]'(by simp [u32Bytes]; omega)) :
    a.ugetUInt32LE off h = v := by
  unfold ugetUInt32LE
  have b0 : a[off.toNat]'(by omega) = v.toUInt8 := by
    simpa [u32Bytes] using hb 0 (by decide)
  have b1 : a[off.toNat + 1]'(by omega) = (v >>> 8).toUInt8 := by
    simpa [u32Bytes] using hb 1 (by decide)
  have b2 : a[off.toNat + 2]'(by omega) = (v >>> 16).toUInt8 := by
    simpa [u32Bytes] using hb 2 (by decide)
  have b3 : a[off.toNat + 3]'(by omega) = (v >>> 24).toUInt8 := by
    simpa [u32Bytes] using hb 3 (by decide)
  simp only [b0, b1, b2, b3]
  exact Regex.VM.Wide.u32_of_le_bytes v

/-- A buffer whose eight bytes are `u64Bytes v` loads as `v`. -/
private theorem ugetUInt64LE_of_bytes (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size)
    (hb : ∀ k, (hk : k < 8) →
      a[off.toNat + k]'(by omega) = (u64Bytes v)[k]'(by simp [u64Bytes]; omega)) :
    a.ugetUInt64LE off h = v := by
  unfold ugetUInt64LE
  have b0 : a[off.toNat]'(by omega) = v.toUInt8 := by
    simpa [u64Bytes] using hb 0 (by decide)
  have b1 : a[off.toNat + 1]'(by omega) = (v >>> 8).toUInt8 := by
    simpa [u64Bytes] using hb 1 (by decide)
  have b2 : a[off.toNat + 2]'(by omega) = (v >>> 16).toUInt8 := by
    simpa [u64Bytes] using hb 2 (by decide)
  have b3 : a[off.toNat + 3]'(by omega) = (v >>> 24).toUInt8 := by
    simpa [u64Bytes] using hb 3 (by decide)
  have b4 : a[off.toNat + 4]'(by omega) = (v >>> 32).toUInt8 := by
    simpa [u64Bytes] using hb 4 (by decide)
  have b5 : a[off.toNat + 5]'(by omega) = (v >>> 40).toUInt8 := by
    simpa [u64Bytes] using hb 5 (by decide)
  have b6 : a[off.toNat + 6]'(by omega) = (v >>> 48).toUInt8 := by
    simpa [u64Bytes] using hb 6 (by decide)
  have b7 : a[off.toNat + 7]'(by omega) = (v >>> 56).toUInt8 := by
    simpa [u64Bytes] using hb 7 (by decide)
  simp only [b0, b1, b2, b3, b4, b5, b6, b7]
  exact Regex.VM.Wide.u64_of_le_bytes v

/-- Two buffers that agree on four bytes load the same `UInt32`. -/
private theorem ugetUInt32LE_congr_bytes (a b : ByteArray) (off : USize)
    (ha : off.toNat + 4 ≤ a.size) (hb : off.toNat + 4 ≤ b.size)
    (hbytes : ∀ k, (hk : k < 4) →
      a[off.toNat + k]'(by omega) = b[off.toNat + k]'(by omega)) :
    a.ugetUInt32LE off ha = b.ugetUInt32LE off hb := by
  unfold ugetUInt32LE
  have b0 : a[off.toNat]'(by omega) = b[off.toNat]'(by omega) := by
    simpa using hbytes 0 (by decide)
  simp only [b0, hbytes 1 (by decide), hbytes 2 (by decide), hbytes 3 (by decide)]

/-- Two buffers that agree on eight bytes load the same `UInt64`. -/
private theorem ugetUInt64LE_congr_bytes (a b : ByteArray) (off : USize)
    (ha : off.toNat + 8 ≤ a.size) (hb : off.toNat + 8 ≤ b.size)
    (hbytes : ∀ k, (hk : k < 8) →
      a[off.toNat + k]'(by omega) = b[off.toNat + k]'(by omega)) :
    a.ugetUInt64LE off ha = b.ugetUInt64LE off hb := by
  unfold ugetUInt64LE
  have b0 : a[off.toNat]'(by omega) = b[off.toNat]'(by omega) := by
    simpa using hbytes 0 (by decide)
  simp only [b0, hbytes 1 (by decide), hbytes 2 (by decide), hbytes 3 (by decide),
    hbytes 4 (by decide), hbytes 5 (by decide), hbytes 6 (by decide), hbytes 7 (by decide)]

/-- The word just written by `usetUInt32LE` reads back as `v`. -/
theorem ugetUInt32LE_uset (a : ByteArray) (off : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.size) :
    (a.usetUInt32LE off v h).ugetUInt32LE off (by rw [usetUInt32LE_size]; exact h) = v := by
  unfold usetUInt32LE
  exact ugetUInt32LE_of_bytes _ off v (by rw [setList_size]; exact h) (fun k hk =>
    setList_get a off.toNat (u32Bytes v) _ k (by simp [u32Bytes]; omega))

/-- A little-endian `UInt32` store leaves a disjoint 4-byte slot unchanged. -/
theorem ugetUInt32LE_uset_disjoint (a : ByteArray) (off off' : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.size) (h' : off'.toNat + 4 ≤ a.size)
    (hdisj : off'.toNat + 4 ≤ off.toNat ∨ off.toNat + 4 ≤ off'.toNat) :
    (a.usetUInt32LE off v h).ugetUInt32LE off' (by rw [usetUInt32LE_size]; exact h') =
      a.ugetUInt32LE off' h' := by
  unfold usetUInt32LE
  exact ugetUInt32LE_congr_bytes _ a off' (by rw [setList_size]; exact h') h' (fun k hk => by
    apply setList_get_out
    simp only [u32Bytes, List.length_cons, List.length_nil]
    cases hdisj with
    | inl hle => omega
    | inr hle => omega)

/-- The slot just written by `usetUInt64LE` reads back as `v`. -/
theorem ugetUInt64LE_uset (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) :
    (a.usetUInt64LE off v h).ugetUInt64LE off (by rw [usetUInt64LE_size]; exact h) = v := by
  unfold usetUInt64LE
  exact ugetUInt64LE_of_bytes _ off v (by rw [setList_size]; exact h) (fun k hk =>
    setList_get a off.toNat (u64Bytes v) _ k (by simp [u64Bytes]; omega))

/-- A little-endian store leaves a disjoint 8-byte slot unchanged. -/
theorem ugetUInt64LE_uset_disjoint (a : ByteArray) (off off' : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off'.toNat + 8 ≤ a.size)
    (hdisj : off'.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ off'.toNat) :
    (a.usetUInt64LE off v h).ugetUInt64LE off' (by rw [usetUInt64LE_size]; exact h') =
      a.ugetUInt64LE off' h' := by
  unfold usetUInt64LE
  exact ugetUInt64LE_congr_bytes _ a off' (by rw [setList_size]; exact h') h' (fun k hk => by
    apply setList_get_out
    simp only [u64Bytes, List.length_cons, List.length_nil]
    cases hdisj with
    | inl hle => omega
    | inr hle => omega)

end ByteArray

namespace Regex.VM.Wide

@[simp]
theorem WordArray.size_eq_data_div (a : WordArray) : a.size = a.data.size / 4 := rfl

theorem WordArray.data_size_push (a : WordArray) (v : UInt32) :
    (a.push v).data.size = a.data.size + 4 := by
  unfold WordArray.push
  simp [ByteArray.pushList_size, ByteArray.u32Bytes]

@[simp]
theorem WordArray.emptyWithCapacity_data_size (n : Nat) :
    (WordArray.emptyWithCapacity n).data.size = 0 := by
  unfold WordArray.emptyWithCapacity ByteArray.emptyWithCapacity
  rfl

theorem WordArray.push_div4 (a : WordArray) (v : UInt32) (h : 4 * a.size = a.data.size) :
    (a.push v).size = a.size + 1 ∧ 4 * (a.push v).size = (a.push v).data.size := by
  have hd := data_size_push a v
  have hs : (a.push v).size = (a.data.size + 4) / 4 := by
    simp [WordArray.size, hd]
  rw [hs, ← h]
  have hdiv : (4 * a.size + 4) / 4 = a.size + 1 := by omega
  refine ⟨hdiv, ?_⟩
  rw [hdiv]
  omega

/-- `nWords * 4 < 2^32` keeps the allocation length inside `USize` on every platform. -/
theorem WordArray.zeros_spec (nWords : Nat) (h : nWords * 4 < 2 ^ 32) :
    (zeros nWords).size = nWords ∧ 4 * (zeros nWords).size = (zeros nWords).data.size := by
  have hn : nWords < 2 ^ 32 := by omega
  have h4 : wordBytes.toNat = 4 := by
    simp [wordBytes, toNat_uSize_ofNat_of_lt 4 (by decide)]
  have hmul : (nWords.toUSize * wordBytes).toNat = nWords * 4 := by
    rw [toNat_mul_of_lt_2_pow_32 (by
      rw [toNat_toUSize_of_lt_2_pow_32 hn, h4]
      exact h), toNat_toUSize_of_lt_2_pow_32 hn, h4]
  unfold zeros WordArray.size
  rw [ByteArray.zero_size, hmul]
  have hdiv : nWords * 4 / 4 = nWords := by omega
  refine ⟨hdiv, ?_⟩
  rw [hdiv]
  omega

@[simp]
theorem WordArray.usetWord_eq (a : WordArray) (i : USize) (v : UInt32)
    (h : (i * wordBytes).toNat + 4 ≤ a.data.size) :
    a.usetWord i v h = a.uset (i * wordBytes) v h := rfl

theorem WordArray.size_uset (a : WordArray) (off : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.data.size) :
    (a.uset off v h).data.size = a.data.size ∧ (a.uset off v h).size = a.size := by
  simp [WordArray.uset, WordArray.size, ByteArray.usetUInt32LE_size]

/-- Reading the word just pushed by `WordArray.push` returns that word. -/
theorem WordArray.uget_push (a : WordArray) (v : UInt32)
    (h : a.data.size.toUSize.toNat + 4 ≤ (a.push v).data.size) (hbase : a.data.size < 2 ^ 32) :
    (a.push v).uget a.data.size.toUSize h = v := by
  unfold WordArray.uget WordArray.push
  have hsz : a.data.size.toUSize.toNat = a.data.size := toNat_toUSize_of_lt_2_pow_32 hbase
  apply ByteArray.ugetUInt32LE_of_bytes
  intro k hk
  have hget := ByteArray.pushList_get a.data (ByteArray.u32Bytes v) k
    (by simp [ByteArray.u32Bytes]; omega)
  have heq : a.data.size + k = a.data.size.toUSize.toNat + k := by rw [hsz]
  exact (ByteArray.get_idx heq _).symm.trans hget

/-- A later `push` does not change a word that was already in range. -/
theorem WordArray.uget_push_lt (a : WordArray) (v : UInt32) (off : USize)
    (h : off.toNat + 4 ≤ a.data.size) :
    (a.push v).uget off (by rw [WordArray.data_size_push]; omega) = a.uget off h := by
  unfold WordArray.uget WordArray.push
  exact ByteArray.ugetUInt32LE_congr_bytes _ a.data off
    (by rw [ByteArray.pushList_size]; simp [ByteArray.u32Bytes]; omega) h (fun k hk =>
      ByteArray.pushList_get_lt a.data _ (off.toNat + k) (by omega))

/-- Reading at equal byte offsets ignores which in-bounds proof is carried. -/
theorem WordArray.uget_off_eq (a : WordArray) (off₁ off₂ : USize)
    (h₁ : off₁.toNat + 4 ≤ a.data.size) (h₂ : off₂.toNat + 4 ≤ a.data.size)
    (heq : off₁ = off₂) : a.uget off₁ h₁ = a.uget off₂ h₂ := by
  subst heq
  rfl

/-- The word just written by `uset` reads back as `v`. -/
theorem WordArray.uget_uset (a : WordArray) (off : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.data.size)
    (h' : off.toNat + 4 ≤ (a.uset off v h).data.size := by
      rw [(size_uset a off v h).1]; exact h) :
    (a.uset off v h).uget off h' = v := by
  unfold WordArray.uget WordArray.uset
  exact ByteArray.ugetUInt32LE_uset a.data off v h

/-- A word store leaves a disjoint word unchanged. -/
theorem WordArray.uget_uset_disjoint (a : WordArray) (off off' : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.data.size) (hread : off'.toNat + 4 ≤ a.data.size)
    (hdisj : off'.toNat + 4 ≤ off.toNat ∨ off.toNat + 4 ≤ off'.toNat)
    (h' : off'.toNat + 4 ≤ (a.uset off v h).data.size := by
      rw [(size_uset a off v h).1]; exact hread) :
    (a.uset off v h).uget off' h' = a.uget off' hread := by
  unfold WordArray.uget WordArray.uset
  exact ByteArray.ugetUInt32LE_uset_disjoint a.data off off' v h hread hdisj

end Regex.VM.Wide

end
