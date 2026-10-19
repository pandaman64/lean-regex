module

public import Init.Data.UInt.Lemmas
public import Regex.Data.String
public import Regex.VM.Wide

open String (Pos PosPlusOne)

/-!
Unboxed replacement for `Buffer` / `BufferStrategy`.

`BufferStrategy.Update` is a `Vector` of `PosPlusOne`. That vector is a heap
object, and an `Array` of them stores pointers, so every save copies a buffer
and adjusts reference counts. Here every capture slot is a little-endian
`UInt64` in one `ByteArray`. The word is a byte offset. The sentinel word is
`utf8ByteSize + 1`, the same offset as `PosPlusOne.sentinel`.

The refined PikeVM is hard-coded to this layout. Rows are contiguous groups of
`nSlots` words: row 0 is the accepted match, row 1 is the match found by the
closure in progress, then two state regions and the ε-stack. Writes land in a
preallocated row, so a save does not allocate.
-/

public section

namespace Regex.VM.FlatBuffer

open Regex.VM.Wide (toNat_toUSize_of_lt_2_pow_32 toNat_uSize_ofNat_of_lt
  toNat_add_of_lt_2_pow_32 toNat_mul_of_lt_2_pow_32 toNat_add_nat_of_lt_2_pow_32)

/-- Eight bytes per capture slot. -/
abbrev slotBytes : USize := 8

/-- Byte offset of row `row` when each row holds `nSlots` slots. -/
@[inline, expose]
def rowOff (row nSlots : USize) : USize :=
  row * nSlots * slotBytes

theorem rowOff_toNat (row slots : USize) (h : row.toNat * slots.toNat * 8 < 2 ^ 32) :
    (rowOff row slots).toNat = row.toNat * slots.toNat * 8 := by
  unfold rowOff slotBytes
  have h8 : (8 : USize).toNat = 8 := toNat_uSize_ofNat_of_lt 8 (by decide)
  have hpair : row.toNat * slots.toNat < 2 ^ 32 := by omega
  rw [toNat_mul_of_lt_2_pow_32 (by rw [toNat_mul_of_lt_2_pow_32 hpair, h8]; omega),
    toNat_mul_of_lt_2_pow_32 hpair, h8]

theorem rowOff_slots_zero (row : USize) : (rowOff row 0).toNat = 0 := by
  rw [rowOff_toNat row 0 (by simp [USize.toNat_zero])]
  simp [USize.toNat_zero]

@[inline, expose]
def uget (a : ByteArray) (off : USize) (h : off.toNat + 8 ≤ a.size) : UInt64 :=
  a.ugetUInt64LE off h

theorem uget_irrel (a : ByteArray) (off : USize)
    (h1 h2 : off.toNat + 8 ≤ a.size) : uget a off h1 = uget a off h2 := rfl

@[inline, expose]
def uset (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) : ByteArray :=
  a.usetUInt64LE off v h

theorem uset_size (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) :
    (uset a off v h).size = a.size := by
  simp [uset, ByteArray.usetUInt64LE_size]

theorem uset_irrel (a : ByteArray) (off : USize) (v : UInt64)
    (h₁ h₂ : off.toNat + 8 ≤ a.size) : uset a off v h₁ = uset a off v h₂ := rfl

theorem uget_uset (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) :
    uget (uset a off v h) off (by rw [uset_size]; exact h) = v := by
  simpa [uget, uset] using ByteArray.ugetUInt64LE_uset a off v h

theorem uget_uset_disjoint (a : ByteArray) (off off' : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off'.toNat + 8 ≤ a.size)
    (hdisj : off'.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ off'.toNat) :
    uget (uset a off v h) off' (by rw [uset_size]; exact h') = uget a off' h' := by
  simpa [uget, uset] using ByteArray.ugetUInt64LE_uset_disjoint a off off' v h h' hdisj

theorem uget_congr (a : ByteArray) (off₁ off₂ : USize) (heq : off₁ = off₂)
    (h₁ : off₁.toNat + 8 ≤ a.size) (h₂ : off₂.toNat + 8 ≤ a.size) :
    uget a off₁ h₁ = uget a off₂ h₂ := by
  subst heq
  exact uget_irrel a off₁ h₁ h₂

theorem uget_uset_self (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off.toNat + 8 ≤ (uset a off v h).size) :
    uget (uset a off v h) off h' = v := by
  have hcanon : uget (uset a off v h) off (by rw [uset_size]; exact h) = v := uget_uset a off v h
  exact uget_irrel (uset a off v h) off (by rw [uset_size]; exact h) h' ▸ hcanon

theorem uget_uset_ne (a : ByteArray) (off off' : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off'.toNat + 8 ≤ a.size)
    (hdisj : off'.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ off'.toNat)
    (hSlot : off'.toNat + 8 ≤ (uset a off v h).size) :
    uget (uset a off v h) off' hSlot = uget a off' h' := by
  have hcanon := uget_uset_disjoint a off off' v h h' hdisj
  exact uget_irrel (uset a off v h) off' (by rw [uset_size]; exact h') hSlot ▸ hcanon

theorem uget_zero (n off : USize) (h : off.toNat + 8 ≤ (ByteArray.zero n).size) :
    uget (ByteArray.zero n) off h = 0 := by
  simpa [uget] using ByteArray.ugetUInt64LE_zero n off h

/-- A slot start is strictly below `2^32` when the whole row window fits in `2^32`. -/
theorem slotOff_lt {base count k : Nat} (hk : k < count) (hfit : base + count * 8 ≤ 2 ^ 32) :
    base + k * 8 < 2 ^ 32 := by
  have : k + 1 ≤ count := Nat.succ_le_of_lt hk
  omega

theorem slotOff_le {base count k size : Nat} (hk : k < count) (h : base + count * 8 ≤ size) :
    base + k * 8 + 8 ≤ size := by
  have : k + 1 ≤ count := Nat.succ_le_of_lt hk
  omega

theorem rowMul8_le {base count : Nat} (h : base + count * 8 ≤ 2 ^ 32) :
    count * 8 ≤ 2 ^ 32 := by
  omega

theorem index_mul8_lt {k count : Nat} (hk : k < count) (h : count * 8 ≤ 2 ^ 32) :
    k * 8 < 2 ^ 32 := by
  omega

theorem index_succ_lt {k count : Nat} (hk : k < count) (h : count * 8 ≤ 2 ^ 32) :
    k + 1 < 2 ^ 32 := by
  omega

theorem toNat_slotBytes : slotBytes.toNat = 8 := by
  unfold slotBytes
  exact toNat_uSize_ofNat_of_lt 8 (by decide)

theorem lt_of_ne_slots {k n : USize} (hk : k.toNat ≤ n.toNat) (hne : k ≠ n) :
    k.toNat < n.toNat :=
  Nat.lt_of_le_of_ne hk (fun h => hne (USize.toNat_inj.mp h))

theorem mul_slotBytes_toNat (k : USize) (hk : k.toNat * 8 < 2 ^ 32) :
    (k * slotBytes).toNat = k.toNat * 8 := by
  rw [toNat_mul_of_lt_2_pow_32 (by rw [toNat_slotBytes]; exact hk), toNat_slotBytes]

/-- `base + k * 8` computed with `USize` arithmetic, which does not wrap under `hsum`. -/
theorem slotAddr_toNat (base k : USize) (hk : k.toNat * 8 < 2 ^ 32)
    (hsum : base.toNat + k.toNat * 8 < 2 ^ 32) :
    (base + k * slotBytes).toNat = base.toNat + k.toNat * 8 := by
  have hm : (k * slotBytes).toNat = k.toNat * 8 := mul_slotBytes_toNat k hk
  rw [toNat_add_of_lt_2_pow_32 (by rw [hm]; exact hsum), hm]

theorem succ_k_toNat (k : USize) (hk : k.toNat + 1 < 2 ^ 32) :
    (k + 1).toNat = k.toNat + 1 :=
  toNat_add_nat_of_lt_2_pow_32 k 1 (by decide) hk

theorem index_hkNext {nSlots k : USize}
    (hRows : nSlots.toNat * 8 ≤ 2 ^ 32)
    (hk : k.toNat ≤ nSlots.toNat) (hne : ¬ k = nSlots) :
    (k + 1).toNat ≤ nSlots.toNat := by
  rw [succ_k_toNat k (index_succ_lt (lt_of_ne_slots hk hne) hRows)]
  exact Nat.succ_le_of_lt (lt_of_ne_slots hk hne)

theorem index_measure {nSlots k : USize}
    (hRows : nSlots.toNat * 8 ≤ 2 ^ 32)
    (hk : k.toNat ≤ nSlots.toNat) (hne : ¬ k = nSlots) :
    nSlots.toNat - (k + 1).toNat < nSlots.toNat - k.toNat := by
  rw [succ_k_toNat k (index_succ_lt (lt_of_ne_slots hk hne) hRows)]
  exact Nat.sub_succ_lt_self _ _ (lt_of_ne_slots hk hne)

/--
Index `k` of a row that still has slots left.

Every row walk rederives the same bounds: `k` is in range, `k * 8` fits in
`USize`, and `k + 1` is the next index. Packing them once is the induction step.
-/
structure IndexStep (nSlots k : USize)
    (hRows : nSlots.toNat * 8 ≤ 2 ^ 32)
    (hk : k.toNat ≤ nSlots.toNat) (hne : ¬ k = nSlots) where
  hlt : k.toNat < nSlots.toNat := lt_of_ne_slots hk hne
  hMul : k.toNat * 8 < 2 ^ 32 := index_mul8_lt (lt_of_ne_slots hk hne) hRows
  hNext : (k + 1).toNat = k.toNat + 1 :=
    succ_k_toNat k (index_succ_lt (lt_of_ne_slots hk hne) hRows)
  hkNext : (k + 1).toNat ≤ nSlots.toNat := index_hkNext hRows hk hne
  hMeasure : nSlots.toNat - (k + 1).toNat < nSlots.toNat - k.toNat :=
    index_measure hRows hk hne

/--
`k`-th slot of a row, as a `USize`.

`@[inline]` exports the erased-proof specialization. The function is recursive, so
callers are not inlined into the loop; they are rewritten to that specialization.
-/
@[inline, expose]
def copySlots (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size) : ByteArray :=
  if hk' : k = nSlots then
    a
  else
    let step : IndexStep nSlots k (rowMul8_le hSrcFit) hk hk' := {}
    let srcOff := src + k * slotBytes
    let dstOff := dst + k * slotBytes
    have hSrcNat : srcOff.toNat = src.toNat + k.toNat * 8 :=
      slotAddr_toNat src k step.hMul (slotOff_lt step.hlt hSrcFit)
    have hDstNat : dstOff.toNat = dst.toNat + k.toNat * 8 :=
      slotAddr_toNat dst k step.hMul (slotOff_lt step.hlt hDstFit)
    have hRead : srcOff.toNat + 8 ≤ a.size := by rw [hSrcNat]; exact slotOff_le step.hlt hSrc
    have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le step.hlt hDst
    let a' := uset a dstOff (uget a srcOff hRead) hWrite
    have hsize : a'.size = a.size := uset_size a dstOff _ hWrite
    copySlots dst src nSlots hDstFit hSrcFit (k + 1) step.hkNext a'
      (by rw [hsize]; exact hDst) (by rw [hsize]; exact hSrc)
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact step.hMeasure

theorem zero_le_toNat (n : Nat) : (0 : USize).toNat ≤ n := by
  simp [USize.toNat_zero]

/-- Copy `nSlots` slots from byte offset `src` onto `dst`. -/
@[inline, expose]
def copyRow (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32) : ByteArray :=
  copySlots dst src nSlots hDstFit hSrcFit 0 (zero_le_toNat _) a hDst hSrc


/--
`k`-th slot of a filled row. See `copySlots` for why this is `@[inline]` and recursive.
-/
@[inline, expose]
def fillSlots (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size) : ByteArray :=
  if hk' : k = nSlots then
    a
  else
    let step : IndexStep nSlots k (rowMul8_le hFit) hk hk' := {}
    let dstOff := dst + k * slotBytes
    have hDstNat : dstOff.toNat = dst.toNat + k.toNat * 8 :=
      slotAddr_toNat dst k step.hMul (slotOff_lt step.hlt hFit)
    have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le step.hlt hDst
    let a' := uset a dstOff v hWrite
    have hsize : a'.size = a.size := uset_size a dstOff v hWrite
    fillSlots dst nSlots v hFit (k + 1) step.hkNext a' (by rw [hsize]; exact hDst)
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact step.hMeasure

/-- Fill one row with `v`. Used to install an empty (`PosPlusOne.sentinel`) buffer. -/
@[inline, expose]
def fillRow (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32) : ByteArray :=
  fillSlots dst nSlots v hDstFit 0 (zero_le_toNat _) a hDst

/-- Append `rows` zeroed rows. The caller overwrites them before they are read. -/
def growRows (a : ByteArray) (rows nSlots : Nat) : ByteArray :=
  go (rows * nSlots * 8) a
where
  go : Nat → ByteArray → ByteArray
    | 0, a => a
    | n + 1, a => go n (a.push 0)
  termination_by n => n

/-- Sentinel slot: `PosPlusOne.sentinel`. -/
@[inline, expose]
def sentinelWord (s : String) : UInt64 :=
  (s.utf8ByteSize + 1).toUInt64

/-- Byte index of a valid position. -/
@[inline, expose]
def encodePos {s : String} (p : Pos s) : UInt64 :=
  p.offset.byteIdx.toUInt64

/--
A capture word is either the sentinel (`utf8ByteSize + 1`) or the byte index of a
valid position. `NFA.WellFormed` does not state this: saves copy positions the VM
already holds.
-/
@[expose]
def SlotWord (s : String) (w : UInt64) : Prop :=
  w.toNat = s.utf8ByteSize + 1 ∨ ∃ p : Pos s, w.toNat = p.offset.byteIdx


/--
Decode one slot.

A word equal to `sentinelWord` is `PosPlusOne.sentinel`. Any other word was
written by `encodePos` from a valid position.
-/
@[inline]
def decode {s : String} (w : UInt64) (h : SlotWord s w) : PosPlusOne s :=
  if hw : w.toNat = s.utf8ByteSize + 1 then
    .sentinel s
  else
    .pos (String.pos s ⟨w.toNat⟩ (by
      cases h with
      | inl heq => exact absurd heq hw
      | inr hex =>
        obtain ⟨p, hidx⟩ := hex
        have : (⟨w.toNat⟩ : Pos.Raw).byteIdx = p.offset.byteIdx := hidx
        exact (Pos.Raw.ext this).symm ▸ p.isValid))

/-- Row 0 as a `Vector` of positions. One allocation, at the API boundary. -/
def toBuffer {s : String} (a : ByteArray) (nSlots : Nat)
    (hSize : ∀ i : Fin nSlots, (i.val.toUSize * slotBytes).toNat + 8 ≤ a.size)
    (hWord : ∀ i : Fin nSlots, SlotWord s (uget a (i.val.toUSize * slotBytes) (hSize i))) :
    Vector (PosPlusOne s) nSlots :=
  Vector.ofFn fun i : Fin nSlots =>
    decode (uget a (i.val.toUSize * slotBytes) (hSize i)) (hWord i)

end Regex.VM.FlatBuffer

end
