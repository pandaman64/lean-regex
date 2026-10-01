module

public import Init.Data.ByteArray.Lemmas
public import Init.Data.Nat.Bitwise.Lemmas
public import Init.Data.UInt.Bitwise
public import Init.Data.UInt.Lemmas

/-!
Little-endian `UInt32` loads and stores on a `ByteArray`.

The reference bodies and the `@[extern]` split are adapted, with attribution,
from lean-zip's `Zip/Native/Wide.lean` (`ugetUInt32LE` and `usetUInt32LE`):

  https://github.com/kim-em/lean-zip/blob/2f7a63f38195bc667a926881b55d10c9f8a88eeb/Zip/Native/Wide.lean

`@[extern]` replaces the compiled code with one wide load or store in
`c/bytearray_wide_ffi.c`. The reference body remains the specification: four
bytes, little-endian. The offset is a `USize`, so hot-loop index arithmetic
stays unboxed. `WordArray` is the one-field wrapper around that buffer; Lean
erases it, and each word occupies four raw bytes rather than a boxed
`Array` slot.
-/

public section

namespace ByteArray

/-- `set` preserves size. Used to chain the in-bounds proofs of `usetUInt32LE`. -/
protected theorem size_set (a : ByteArray) (i : Nat) (v : UInt8) (h : i < a.size) :
    (a.set i v h).size = a.size := by
  simp only [← ByteArray.size_data, ByteArray.data_set, Array.size_set]

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

/-- `set` at `i` reads back `v`, for whichever in-bounds proof the reader carries. -/
private theorem get_set_self_flex (a : ByteArray) (i : Nat) (v : UInt8) (hi : i < a.size)
    (hi' : i < (a.set i v hi).size := by simp only [ByteArray.size_set]; omega) :
    (a.set i v hi)[i]'hi' = v :=
  (get_irrel (a.set i v hi) i hi' (by rw [ByteArray.size_set]; exact hi)).trans (get_set_self a i v hi)

/-- `set` at `i` leaves every other in-range byte unchanged. -/
private theorem get_set_skip (a : ByteArray) (i j : Nat) (v : UInt8)
    (hi : i < a.size)
    (hj : j < a.size := by first | omega | simp only [ByteArray.size_set]; omega)
    (hne : i ≠ j := by omega)
    (hj' : j < (a.set i v hi).size := by simp only [ByteArray.size_set]; omega) :
    (a.set i v hi)[j]'hj' = a[j] :=
  (get_irrel (a.set i v hi) j hj' (by rw [ByteArray.size_set]; exact hj)).trans
    (get_set_ne a i j v hi hj hne)

/--
Load the little-endian `UInt32` at byte offset `off`.

The reference body is the trusted specification of the `@[extern]`. The C
implementation reads those four bytes in one wide load.
-/
@[extern "lean_regex_uget_u32le"]
def ugetUInt32LE (a : @& ByteArray) (off : USize)
    (h : off.toNat + 4 ≤ a.size := by get_elem_tactic) : UInt32 :=
  (a[off.toNat]'(by omega)).toUInt32 |||
    ((a[off.toNat + 1]'(by omega)).toUInt32 <<< 8) |||
    ((a[off.toNat + 2]'(by omega)).toUInt32 <<< 16) |||
    ((a[off.toNat + 3]'(by omega)).toUInt32 <<< 24)

/--
Store the little-endian `UInt32` `v` at byte offset `off`.

The reference body is four `ByteArray.set`s. The C implementation writes an
exclusive buffer in place and copies a shared buffer first.
-/
@[extern "lean_regex_uset_u32le"]
def usetUInt32LE (a : ByteArray) (off : USize) (v : UInt32)
    (h : off.toNat + 4 ≤ a.size := by get_elem_tactic) : ByteArray :=
  ((((a.set off.toNat v.toUInt8 (by omega)).set
        (off.toNat + 1) (v >>> 8).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 2) (v >>> 16).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 3) (v >>> 24).toUInt8 (by simp only [ByteArray.size_set]; omega))

/--
Load the little-endian `UInt64` at byte offset `off`.

Capture slots in the refined PikeVM are byte offsets. A `UInt32` would truncate
a string longer than 4 GiB; eight bytes cover every index that fits in this
runtime. The reference body is the specification. The C implementation reads
those eight bytes in one wide load.
-/
@[extern "lean_regex_uget_u64le"]
def ugetUInt64LE (a : @& ByteArray) (off : USize)
    (h : off.toNat + 8 ≤ a.size := by get_elem_tactic) : UInt64 :=
  (a[off.toNat]'(by omega)).toUInt64 |||
    ((a[off.toNat + 1]'(by omega)).toUInt64 <<< 8) |||
    ((a[off.toNat + 2]'(by omega)).toUInt64 <<< 16) |||
    ((a[off.toNat + 3]'(by omega)).toUInt64 <<< 24) |||
    ((a[off.toNat + 4]'(by omega)).toUInt64 <<< 32) |||
    ((a[off.toNat + 5]'(by omega)).toUInt64 <<< 40) |||
    ((a[off.toNat + 6]'(by omega)).toUInt64 <<< 48) |||
    ((a[off.toNat + 7]'(by omega)).toUInt64 <<< 56)

/--
Store the little-endian `UInt64` `v` at byte offset `off`.

The reference body is eight `ByteArray.set`s. The C implementation writes an
exclusive buffer in place and copies a shared buffer first.
-/
@[extern "lean_regex_uset_u64le"]
def usetUInt64LE (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size := by get_elem_tactic) : ByteArray :=
  ((((((((a.set off.toNat v.toUInt8 (by omega)).set
        (off.toNat + 1) (v >>> 8).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 2) (v >>> 16).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 3) (v >>> 24).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 4) (v >>> 32).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 5) (v >>> 40).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 6) (v >>> 48).toUInt8 (by simp only [ByteArray.size_set]; omega)).set
        (off.toNat + 7) (v >>> 56).toUInt8 (by simp only [ByteArray.size_set]; omega))

theorem usetUInt64LE_size (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) :
    (a.usetUInt64LE off v h).size = a.size := by
  simp [usetUInt64LE, ByteArray.size_set]

/--
`n` zero bytes.

The reference body is `n` pushes. The C implementation allocates one scalar
array and clears it. Callers allocate scratch as one block, so the
compiled path must not walk the bytes in Lean.
-/
@[extern "lean_regex_zero_byte_array"]
def zero (n : USize) : ByteArray :=
  go n.toNat .empty
where
  go : Nat → ByteArray → ByteArray
    | 0, a => a
    | i + 1, a => go i (a.push 0)
  termination_by i => i

end ByteArray

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

/--
Flat little-endian word buffer.

The single field is erased, so a `WordArray` is the underlying `ByteArray` at
runtime. Word `i` occupies bytes `4*i .. 4*i+3`.
-/
structure WordArray where
  data : ByteArray

/-- Four bytes per stored `UInt32`. -/
abbrev wordBytes : USize := 4

def WordArray.emptyWithCapacity (nWords : Nat) : WordArray :=
  ⟨ByteArray.emptyWithCapacity (nWords * 4)⟩

/-- Number of stored words. -/
@[expose]
def WordArray.size (a : WordArray) : Nat :=
  a.data.size / 4

theorem WordArray.size_eq_data_div (a : WordArray) : a.size = a.data.size / 4 := rfl

def WordArray.push (a : WordArray) (v : UInt32) : WordArray :=
  ⟨a.data.push v.toUInt8
      |>.push (v >>> 8).toUInt8
      |>.push (v >>> 16).toUInt8
      |>.push (v >>> 24).toUInt8⟩

theorem WordArray.data_size_push (a : WordArray) (v : UInt32) :
    (a.push v).data.size = a.data.size + 4 := by
  simp [push, ByteArray.size_push]

theorem WordArray.emptyWithCapacity_data_size (n : Nat) :
    (WordArray.emptyWithCapacity n).data.size = 0 := by
  unfold emptyWithCapacity ByteArray.emptyWithCapacity
  rfl

private theorem orLow (low high i : Nat) (hlt : low < 2 ^ i) :
    low ||| (high <<< i) = low + high * 2 ^ i := by
  rw [Nat.shiftLeft_eq, Nat.mul_comm high (2 ^ i), Nat.or_comm]
  exact Nat.add_comm _ _ ▸ (Nat.two_pow_add_eq_or_of_lt hlt high).symm

private theorem shiftRight_add (a k m : Nat) : (a >>> k) >>> m = a >>> (k + m) := by
  simp [Nat.shiftRight_eq_div_pow, Nat.div_div_eq_div_mul, ← Nat.pow_add]

private theorem splitByte (m : Nat) : m = m % 256 + (m >>> 8) * 256 := by
  have e : (256 : Nat) = 2 ^ 8 := by decide
  rw [e, Nat.shiftRight_eq_div_pow, Nat.mul_comm]
  exact (Nat.mod_add_div m (2 ^ 8)).symm

/-- Four little-endian bytes reassemble the original `UInt32`. -/
private theorem u32_of_le_bytes (v : UInt32) :
    v.toUInt8.toUInt32 |||
      ((v >>> 8).toUInt8.toUInt32 <<< 8) |||
      ((v >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((v >>> 24).toUInt8.toUInt32 <<< 24) = v := by
  apply UInt32.toNat_inj.mp
  have h8 : (8 : UInt32).toNat = 8 := by decide
  have h16 : (16 : UInt32).toNat = 16 := by decide
  have h24 : (24 : UInt32).toNat = 24 := by decide
  simp only [UInt32.toNat_or, UInt32.toNat_shiftLeft, UInt32.toNat_shiftRight,
    UInt32.toNat_toUInt8, UInt8.toNat_toUInt32, h8, h16, h24,
    show 8 % 32 = 8 by decide, show 16 % 32 = 16 by decide, show 24 % 32 = 24 by decide]
  have modShift (b k : Nat) (hb : b < 256) (hk : k ≤ 24) : (b <<< k) % 2 ^ 32 = b <<< k := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    have hb' : b ≤ 255 := Nat.lt_succ_iff.mp hb
    have hmul : b * 2 ^ k ≤ 255 * 2 ^ 24 :=
      Nat.mul_le_mul hb' (Nat.pow_le_pow_right (by decide) hk)
    have h255 : 255 * 2 ^ 24 < 2 ^ 32 := by decide
    omega
  have hb1 : v.toNat >>> 8 % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb2 : v.toNat >>> 16 % 256 < 256 := Nat.mod_lt _ (by decide)
  have hb3 : v.toNat >>> 24 % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [modShift _ 8 hb1 (by decide), modShift _ 16 hb2 (by decide), modShift _ 24 hb3 (by decide)]
  have assemble (n : Nat) (hn : n < 2 ^ 32) :
      n % 256 ||| (n >>> 8 % 256) <<< 8 ||| (n >>> 16 % 256) <<< 16 ||| (n >>> 24 % 256) <<< 24 = n := by
    have hz : n >>> 32 = 0 := Nat.shiftRight_eq_zero n 32 hn
    have s24 : n >>> 24 = n >>> 24 % 256 := by
      have h := splitByte (n >>> 24)
      rw [shiftRight_add n 24 8, show 24 + 8 = 32 by decide, hz, Nat.zero_mul, Nat.add_zero] at h
      exact h
    have s16 : n >>> 16 = n >>> 16 % 256 + (n >>> 24 % 256) * 256 := by
      have h := splitByte (n >>> 16)
      rw [shiftRight_add n 16 8, show 16 + 8 = 24 by decide, s24] at h
      exact h
    have s8 : n >>> 8 = n >>> 8 % 256 + (n >>> 16) * 256 := by
      have h := splitByte (n >>> 8)
      rw [shiftRight_add n 8 8, show 8 + 8 = 16 by decide] at h
      exact h
    have sum :
        n = n % 256 + (n >>> 8 % 256) * 256 + (n >>> 16 % 256) * 65536 +
          (n >>> 24 % 256) * 16777216 := by
      have h := splitByte n
      rw [s8, Nat.right_distrib, Nat.mul_assoc] at h
      rw [show 256 * 256 = 65536 by decide, s16, Nat.right_distrib, Nat.mul_assoc] at h
      rw [show 256 * 65536 = 16777216 by decide] at h
      omega
    have e8 : (256 : Nat) = 2 ^ 8 := by decide
    have b0 : n % 256 < 2 ^ 8 := by simpa [e8] using Nat.mod_lt n (by decide : 0 < 256)
    have low8 : n % 256 + (n >>> 8 % 256) * 2 ^ 8 < 2 ^ 16 := by
      have hb0 : n % 256 ≤ 255 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      have hb1 : n >>> 8 % 256 ≤ 255 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      omega
    have low16 : n % 256 + (n >>> 8 % 256) * 2 ^ 8 + (n >>> 16 % 256) * 2 ^ 16 < 2 ^ 24 := by
      have hb0 : n % 256 ≤ 255 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      have hb1 : n >>> 8 % 256 ≤ 255 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      have hb2 : n >>> 16 % 256 ≤ 255 := Nat.lt_succ_iff.mp (Nat.mod_lt _ (by decide))
      omega
    have h01 := orLow (n % 256) (n >>> 8 % 256) 8 b0
    have h012 := orLow (n % 256 ||| (n >>> 8 % 256) <<< 8) (n >>> 16 % 256) 16 (by rwa [h01])
    have h0123 := orLow ((n % 256 ||| (n >>> 8 % 256) <<< 8) ||| (n >>> 16 % 256) <<< 16)
        (n >>> 24 % 256) 24 (by rwa [h012, h01])
    rw [h0123, h012, h01, ← sum]
  exact assemble v.toNat (UInt32.toNat_lt v)

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

private theorem u64_nat (n : Nat) (hn : n < 2 ^ 64) :
    n % 256 ||| (n >>> 8 % 256) <<< 8 ||| (n >>> 16 % 256) <<< 16 ||| (n >>> 24 % 256) <<< 24 |||
      (n >>> 32 % 256) <<< 32 ||| (n >>> 40 % 256) <<< 40 ||| (n >>> 48 % 256) <<< 48 |||
      (n >>> 56 % 256) <<< 56 = n := by
  have hpack : packBytes n 8 =
      n % 256 ||| (n >>> 8 % 256) <<< 8 ||| (n >>> 16 % 256) <<< 16 ||| (n >>> 24 % 256) <<< 24 |||
        (n >>> 32 % 256) <<< 32 ||| (n >>> 40 % 256) <<< 40 ||| (n >>> 48 % 256) <<< 48 |||
        (n >>> 56 % 256) <<< 56 := by
    simp [packBytes, Nat.shiftLeft_zero, Nat.shiftRight_zero, Nat.zero_or]
  rw [← hpack, packBytes_mod, show (8 : Nat) * 8 = 64 by decide]
  exact Nat.mod_eq_of_lt hn

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
  have modShift (b k : Nat) (hb : b < 256) (hk : k ≤ 56) : (b <<< k) % 2 ^ 64 = b <<< k := by
    apply Nat.mod_eq_of_lt
    rw [Nat.shiftLeft_eq]
    have hb' : b ≤ 255 := Nat.lt_succ_iff.mp hb
    have hmul : b * 2 ^ k ≤ 255 * 2 ^ 56 :=
      Nat.mul_le_mul hb' (Nat.pow_le_pow_right (by decide) hk)
    have h255 : 255 * 2 ^ 56 < 2 ^ 64 := by decide
    omega
  have hb (k : Nat) : v.toNat >>> k % 256 < 256 := Nat.mod_lt _ (by decide)
  rw [modShift _ 8 (hb 8) (by decide), modShift _ 16 (hb 16) (by decide),
    modShift _ 24 (hb 24) (by decide), modShift _ 32 (hb 32) (by decide),
    modShift _ 40 (hb 40) (by decide), modShift _ 48 (hb 48) (by decide),
    modShift _ 56 (hb 56) (by decide)]
  exact u64_nat v.toNat (UInt64.toNat_lt v)

@[simp]
private theorem ByteArray.get_push_lt (a : ByteArray) (b : UInt8) (i : Nat) (hi : i < a.size) :
    (a.push b)[i]'(by rw [ByteArray.size_push]; omega) = a[i] := by
  simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, Array.getElem_push_lt hi]

@[simp]
private theorem ByteArray.get_push_eq (a : ByteArray) (b : UInt8) :
    (a.push b)[a.size]'(by rw [ByteArray.size_push]; omega) = b := by
  simp [ByteArray.getElem_eq_getElem_data, ByteArray.data_push, ← ByteArray.size_data,
    Array.getElem_push_eq]

/-- `nWords` zeros, one allocation. -/
def WordArray.zeros (nWords : Nat) : WordArray :=
  ⟨ByteArray.zero (nWords.toUSize * wordBytes)⟩

def WordArray.replicate (n : Nat) (v : UInt32) : WordArray :=
  if v == 0 then
    WordArray.zeros n
  else
    go n (WordArray.emptyWithCapacity n)
where
  go : Nat → WordArray → WordArray
    | 0, a => a
    | i + 1, a => go i (a.push v)
  termination_by i => i

/-- Read the word at byte offset `off`. `off` is a multiple of 4 and in range. -/
@[inline]
def WordArray.uget (a : WordArray) (off : USize) (h : off.toNat + 4 ≤ a.data.size) : UInt32 :=
  a.data.ugetUInt32LE off h

/-- Write the word at byte offset `off`. -/
@[inline]
def WordArray.uset (a : WordArray) (off : USize) (v : UInt32) (h : off.toNat + 4 ≤ a.data.size) :
    WordArray :=
  ⟨a.data.usetUInt32LE off v h⟩

/-- Read word index `i`. -/
@[inline]
def WordArray.ugetWord (a : WordArray) (i : USize) (h : (i * wordBytes).toNat + 4 ≤ a.data.size) :
    UInt32 :=
  a.uget (i * wordBytes) h

/-- Write word index `i`. -/
@[inline]
def WordArray.usetWord (a : WordArray) (i : USize) (v : UInt32)
    (h : (i * wordBytes).toNat + 4 ≤ a.data.size) : WordArray :=
  a.uset (i * wordBytes) v h

private theorem ByteArray.get_push4_lt (a : ByteArray) (b0 b1 b2 b3 : UInt8) (i : Nat)
    (hi : i < a.size) :
    ((((a.push b0).push b1).push b2).push b3)[i]'(by simp only [ByteArray.size_push]; omega) = a[i] := by
  have h1 : i < (a.push b0).size := by rw [ByteArray.size_push]; omega
  have h2 : i < ((a.push b0).push b1).size := by rw [ByteArray.size_push, ByteArray.size_push]; omega
  have h3 : i < (((a.push b0).push b1).push b2).size := by
    rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega
  exact (ByteArray.get_push_lt _ b3 i h3).trans
    ((ByteArray.get_push_lt _ b2 i h2).trans
      ((ByteArray.get_push_lt _ b1 i h1).trans (ByteArray.get_push_lt a b0 i hi)))

private theorem ByteArray.get_push4_eq0 (a : ByteArray) (b0 b1 b2 b3 : UInt8) :
    ((((a.push b0).push b1).push b2).push b3)[a.size]'(by simp only [ByteArray.size_push]; omega) = b0 := by
  have h1 : a.size < (a.push b0).size := by rw [ByteArray.size_push]; omega
  have h2 : a.size < ((a.push b0).push b1).size := by
    rw [ByteArray.size_push, ByteArray.size_push]; omega
  have h3 : a.size < (((a.push b0).push b1).push b2).size := by
    rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega
  exact (ByteArray.get_push_lt _ b3 a.size h3).trans
    ((ByteArray.get_push_lt _ b2 a.size h2).trans
      ((ByteArray.get_push_lt _ b1 a.size h1).trans (ByteArray.get_push_eq a b0)))

private theorem ByteArray.get_push_eq_idx (a : ByteArray) (b : UInt8) (i : Nat) (hi : i = a.size) :
    (a.push b)[i]'(by rw [hi, ByteArray.size_push]; omega) = b := by
  subst hi
  exact ByteArray.get_push_eq a b

private theorem ByteArray.get_push4_eq1 (a : ByteArray) (b0 b1 b2 b3 : UInt8) :
    ((((a.push b0).push b1).push b2).push b3)[a.size + 1]'(by simp only [ByteArray.size_push]; omega) =
      b1 := by
  have h2 : a.size + 1 < ((a.push b0).push b1).size := by
    rw [ByteArray.size_push, ByteArray.size_push]; omega
  have h3 : a.size + 1 < (((a.push b0).push b1).push b2).size := by
    rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega
  have hs : a.size + 1 = (a.push b0).size := by rw [ByteArray.size_push]
  exact (ByteArray.get_push_lt _ b3 (a.size + 1) h3).trans
    ((ByteArray.get_push_lt _ b2 (a.size + 1) h2).trans
      (ByteArray.get_push_eq_idx (a.push b0) b1 (a.size + 1) hs))

private theorem ByteArray.get_push4_eq2 (a : ByteArray) (b0 b1 b2 b3 : UInt8) :
    ((((a.push b0).push b1).push b2).push b3)[a.size + 2]'(by simp only [ByteArray.size_push]; omega) =
      b2 := by
  have h3 : a.size + 2 < (((a.push b0).push b1).push b2).size := by
    rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]; omega
  have hs : a.size + 2 = ((a.push b0).push b1).size := by
    rw [ByteArray.size_push, ByteArray.size_push]
  exact (ByteArray.get_push_lt _ b3 (a.size + 2) h3).trans
    (ByteArray.get_push_eq_idx ((a.push b0).push b1) b2 (a.size + 2) hs)

private theorem ByteArray.get_push4_eq3 (a : ByteArray) (b0 b1 b2 b3 : UInt8) :
    ((((a.push b0).push b1).push b2).push b3)[a.size + 3]'(by simp only [ByteArray.size_push]; omega) =
      b3 := by
  have hs : a.size + 3 = (((a.push b0).push b1).push b2).size := by
    rw [ByteArray.size_push, ByteArray.size_push, ByteArray.size_push]
  exact ByteArray.get_push_eq_idx (((a.push b0).push b1).push b2) b3 (a.size + 3) hs

/-- Reading the word just pushed by `WordArray.push` returns that word. -/
theorem WordArray.uget_push (a : WordArray) (v : UInt32)
    (h : a.data.size.toUSize.toNat + 4 ≤ (a.push v).data.size) (hbase : a.data.size < 2 ^ 32) :
    (a.push v).uget a.data.size.toUSize h = v := by
  unfold WordArray.uget
  have hd : (a.push v).data =
      (((a.data.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push
        (v >>> 24).toUInt8 := by
    simp [WordArray.push]
  have h' : a.data.size.toUSize.toNat + 4 ≤
      ((((a.data.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push
        (v >>> 24).toUInt8).size := by
    simpa [hd] using h
  unfold ByteArray.ugetUInt32LE
  simp only [hd, toNat_toUSize_of_lt_2_pow_32 hbase,
    ByteArray.get_push4_eq0 a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8,
    ByteArray.get_push4_eq1 a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8,
    ByteArray.get_push4_eq2 a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8,
    ByteArray.get_push4_eq3 a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8]
  exact u32_of_le_bytes v

/-- A later `push` does not change a word that was already in range. -/
theorem WordArray.uget_push_lt (a : WordArray) (v : UInt32) (off : USize)
    (h : off.toNat + 4 ≤ a.data.size) :
    (a.push v).uget off (by rw [WordArray.data_size_push]; omega) = a.uget off h := by
  unfold WordArray.uget ByteArray.ugetUInt32LE
  have hd : (a.push v).data =
      (((a.data.push v.toUInt8).push (v >>> 8).toUInt8).push (v >>> 16).toUInt8).push
        (v >>> 24).toUInt8 := by
    simp [WordArray.push]
  simp only [hd,
    ByteArray.get_push4_lt a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      off.toNat (by omega),
    ByteArray.get_push4_lt a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      (off.toNat + 1) (by omega),
    ByteArray.get_push4_lt a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      (off.toNat + 2) (by omega),
    ByteArray.get_push4_lt a.data v.toUInt8 (v >>> 8).toUInt8 (v >>> 16).toUInt8 (v >>> 24).toUInt8
      (off.toNat + 3) (by omega)]

end Regex.VM.Wide

namespace ByteArray

/-- The slot just written by `usetUInt64LE` reads back as `v`. -/
theorem ugetUInt64LE_uset (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) :
    (a.usetUInt64LE off v h).ugetUInt64LE off (by rw [usetUInt64LE_size]; exact h) = v := by
  unfold ugetUInt64LE
  have b0 : (a.usetUInt64LE off v h)[off.toNat]'(by rw [usetUInt64LE_size]; omega) = v.toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b1 : (a.usetUInt64LE off v h)[off.toNat + 1]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 8).toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b2 : (a.usetUInt64LE off v h)[off.toNat + 2]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 16).toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b3 : (a.usetUInt64LE off v h)[off.toNat + 3]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 24).toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b4 : (a.usetUInt64LE off v h)[off.toNat + 4]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 32).toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b5 : (a.usetUInt64LE off v h)[off.toNat + 5]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 40).toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b6 : (a.usetUInt64LE off v h)[off.toNat + 6]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 48).toUInt8 := by
    unfold usetUInt64LE
    exact (get_set_skip _ _ _ _ _).trans <|
      get_set_self_flex _ _ _ _
  have b7 : (a.usetUInt64LE off v h)[off.toNat + 7]'(by rw [usetUInt64LE_size]; omega) =
      (v >>> 56).toUInt8 := by
    unfold usetUInt64LE
    exact get_set_self_flex _ _ _ _
  simp only [b0, b1, b2, b3, b4, b5, b6, b7]
  exact Regex.VM.Wide.u64_of_le_bytes v

private theorem usetUInt64LE_get_outside (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (j : Nat) (hj : j < a.size)
    (hout : j < off.toNat ∨ off.toNat + 8 ≤ j) :
    (a.usetUInt64LE off v h)[j]'(by rw [usetUInt64LE_size]; exact hj) = a[j] := by
  unfold usetUInt64LE
  exact (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans <|
    (get_set_skip _ _ _ _ _).trans rfl

/-- A little-endian store leaves a disjoint 8-byte slot unchanged. -/
theorem ugetUInt64LE_uset_disjoint (a : ByteArray) (off off' : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off'.toNat + 8 ≤ a.size)
    (hdisj : off'.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ off'.toNat) :
    (a.usetUInt64LE off v h).ugetUInt64LE off' (by rw [usetUInt64LE_size]; exact h') =
      a.ugetUInt64LE off' h' := by
  unfold ugetUInt64LE
  have bout (k : Nat) (hk : k < 8) :
      (a.usetUInt64LE off v h)[off'.toNat + k]'(by rw [usetUInt64LE_size]; omega) =
        a[off'.toNat + k]'(by omega) := by
    have hout : off'.toNat + k < off.toNat ∨ off.toNat + 8 ≤ off'.toNat + k := by
      cases hdisj with
      | inl hle => omega
      | inr hle => omega
    exact usetUInt64LE_get_outside a off v h (off'.toNat + k) (by omega) hout
  have b0 : (a.usetUInt64LE off v h)[off'.toNat]'(by rw [usetUInt64LE_size]; omega) =
      a[off'.toNat]'(by omega) :=
    usetUInt64LE_get_outside a off v h off'.toNat (by omega) (by
      cases hdisj with
      | inl hle => omega
      | inr hle => omega)
  simp only [b0, bout 1 (by decide), bout 2 (by decide), bout 3 (by decide),
    bout 4 (by decide), bout 5 (by decide), bout 6 (by decide), bout 7 (by decide)]

end ByteArray

end
