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

open Regex.VM.Wide (toNat_toUSize_of_lt_2_pow_32)

/-- Eight bytes per capture slot. -/
abbrev slotBytes : USize := 8

/-- Byte offset of row `row` when each row holds `nSlots` slots. -/
@[inline]
def rowOff (row nSlots : USize) : USize :=
  row * nSlots * slotBytes

@[inline]
def uget (a : ByteArray) (off : USize) (h : off.toNat + 8 ≤ a.size) : UInt64 :=
  a.ugetUInt64LE off h

private theorem uget_irrel (a : ByteArray) (off : USize)
    (h1 h2 : off.toNat + 8 ≤ a.size) : uget a off h1 = uget a off h2 := rfl

@[inline]
def uset (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) : ByteArray :=
  a.usetUInt64LE off v h

theorem uset_size (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) :
    (uset a off v h).size = a.size := by
  simp [uset, ByteArray.usetUInt64LE_size]

private theorem uget_uset (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) :
    uget (uset a off v h) off (by rw [uset_size]; exact h) = v := by
  simpa [uget, uset] using ByteArray.ugetUInt64LE_uset a off v h

private theorem uget_uset_disjoint (a : ByteArray) (off off' : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off'.toNat + 8 ≤ a.size)
    (hdisj : off'.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ off'.toNat) :
    uget (uset a off v h) off' (by rw [uset_size]; exact h') = uget a off' h' := by
  simpa [uget, uset] using ByteArray.ugetUInt64LE_uset_disjoint a off off' v h h' hdisj

/-- A slot start is strictly below `2^32` when the whole row window fits in `2^32`. -/
private theorem slotOff_lt {base count k : Nat} (hk : k < count) (hfit : base + count * 8 ≤ 2 ^ 32) :
    base + k * 8 < 2 ^ 32 := by
  have : k + 1 ≤ count := Nat.succ_le_of_lt hk
  omega

private theorem slotOff_le {base count k size : Nat} (hk : k < count) (h : base + count * 8 ≤ size) :
    base + k * 8 + 8 ≤ size := by
  have : k + 1 ≤ count := Nat.succ_le_of_lt hk
  omega

/-- Copy `nSlots` slots from byte offset `src` onto `dst`. -/
def copyRow (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32) : ByteArray :=
  go 0 (Nat.zero_le _) a hDst hSrc
where
  go (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
      (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
      (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size) : ByteArray :=
    if hk' : k = nSlots.toNat then
      a
    else
      have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
      have hSrcLt : src.toNat + k * 8 < 2 ^ 32 := slotOff_lt hlt hSrcFit
      have hDstLt : dst.toNat + k * 8 < 2 ^ 32 := slotOff_lt hlt hDstFit
      let srcOff := (src.toNat + k * 8).toUSize
      let dstOff := (dst.toNat + k * 8).toUSize
      have hSrcNat : srcOff.toNat = src.toNat + k * 8 := toNat_toUSize_of_lt_2_pow_32 hSrcLt
      have hDstNat : dstOff.toNat = dst.toNat + k * 8 := toNat_toUSize_of_lt_2_pow_32 hDstLt
      have hRead : srcOff.toNat + 8 ≤ a.size := by rw [hSrcNat]; exact slotOff_le hlt hSrc
      have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le hlt hDst
      let a' := uset a dstOff (uget a srcOff hRead) hWrite
      have hsize : a'.size = a.size := uset_size a dstOff _ hWrite
      go (k + 1) (Nat.succ_le_of_lt hlt) a' (by rw [hsize]; exact hDst) (by rw [hsize]; exact hSrc)
  termination_by nSlots.toNat - k

private theorem copyRow.go_size (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size) :
    (copyRow.go dst src nSlots hDstFit hSrcFit k hk a hDst hSrc).size = a.size := by
  unfold copyRow.go
  by_cases hk' : k = nSlots.toNat
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    exact (copyRow.go_size dst src nSlots hDstFit hSrcFit (k + 1)
      (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk hk'))
      (uset a ((dst.toNat + k * 8).toUSize)
        (uget a ((src.toNat + k * 8).toUSize) (by
          rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt (Nat.lt_of_le_of_ne hk hk') hSrcFit)]
          exact slotOff_le (Nat.lt_of_le_of_ne hk hk') hSrc))
        (by
          rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt (Nat.lt_of_le_of_ne hk hk') hDstFit)]
          exact slotOff_le (Nat.lt_of_le_of_ne hk hk') hDst))
      (by rw [uset_size]; exact hDst) (by rw [uset_size]; exact hSrc)).trans
      (uset_size _ _ _ _)
termination_by nSlots.toNat - k

/-- A slot disjoint from the not-yet-copied suffix of the destination row is left unchanged. -/
private theorem copyRow.go_outside (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat + k * 8 ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat) :
    uget (copyRow.go dst src nSlots hDstFit hSrcFit k hk a hDst hSrc) off
        (by rw [copyRow.go_size dst src nSlots hDstFit hSrcFit k hk a hDst hSrc]; exact hoff) =
      uget a off hoff := by
  unfold copyRow.go
  by_cases hk' : k = nSlots.toNat
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
    have hSrcNat : ((src.toNat + k * 8).toUSize).toNat = src.toNat + k * 8 :=
      toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hlt hSrcFit)
    have hDstNat : ((dst.toNat + k * 8).toUSize).toNat = dst.toNat + k * 8 :=
      toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hlt hDstFit)
    have hRead : ((src.toNat + k * 8).toUSize).toNat + 8 ≤ a.size := by
      rw [hSrcNat]; exact slotOff_le hlt hSrc
    have hWrite : ((dst.toNat + k * 8).toUSize).toNat + 8 ≤ a.size := by
      rw [hDstNat]; exact slotOff_le hlt hDst
    let srcOff := (src.toNat + k * 8).toUSize
    let dstOff := (dst.toNat + k * 8).toUSize
    let a' := uset a dstOff (uget a srcOff hRead) hWrite
    have hWriteDisj : off.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + 8 ≤ off.toNat := by
      cases hdisj with
      | inl hle =>
        rw [hDstNat]
        exact Or.inl hle
      | inr hge =>
        right
        rw [hDstNat]
        have hk1 : k + 1 ≤ nSlots.toNat := Nat.succ_le_of_lt hlt
        omega
    have hdisj' : off.toNat + 8 ≤ dst.toNat + (k + 1) * 8 ∨
        dst.toNat + nSlots.toNat * 8 ≤ off.toNat := by
      cases hdisj with
      | inl hle =>
        left
        omega
      | inr hge =>
        exact Or.inr hge
    have hRec := copyRow.go_outside dst src nSlots hDstFit hSrcFit (k + 1)
      (Nat.succ_le_of_lt hlt) a' (by rw [uset_size]; exact hDst) (by rw [uset_size]; exact hSrc)
      off (by rw [uset_size]; exact hoff) hdisj'
    have hKeep := uget_uset_disjoint a dstOff off (uget a srcOff hRead) hWrite hoff hWriteDisj
    exact (uget_irrel _ _ _ _).trans (hRec.trans hKeep)
termination_by nSlots.toNat - k

/--
Slot `j` of the suffix still to be copied equals slot `j` of the source, when the two
windows are the same row or do not overlap.
-/
private theorem copyRow.go_uget (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hsep : dst.toNat = src.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ src.toNat ∨
      src.toNat + nSlots.toNat * 8 ≤ dst.toNat)
    (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (j : Nat) (hj : j < nSlots.toNat) (hkj : k ≤ j) :
    uget (copyRow.go dst src nSlots hDstFit hSrcFit k hk a hDst hSrc) ((dst.toNat + j * 8).toUSize)
      (by
        rw [copyRow.go_size dst src nSlots hDstFit hSrcFit k hk a hDst hSrc]
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hDstFit)]
        exact slotOff_le hj hDst) =
      uget a ((src.toNat + j * 8).toUSize) (by
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hSrcFit)]
        exact slotOff_le hj hSrc) := by
  unfold copyRow.go
  by_cases hk' : k = nSlots.toNat
  · simp only [hk'] at hkj
    omega
  · simp only [hk', ↓reduceDIte]
    have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
    have hSrcNat : ((src.toNat + k * 8).toUSize).toNat = src.toNat + k * 8 :=
      toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hlt hSrcFit)
    have hDstNat : ((dst.toNat + k * 8).toUSize).toNat = dst.toNat + k * 8 :=
      toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hlt hDstFit)
    have hRead : ((src.toNat + k * 8).toUSize).toNat + 8 ≤ a.size := by
      rw [hSrcNat]; exact slotOff_le hlt hSrc
    have hWrite : ((dst.toNat + k * 8).toUSize).toNat + 8 ≤ a.size := by
      rw [hDstNat]; exact slotOff_le hlt hDst
    let srcOff := (src.toNat + k * 8).toUSize
    let dstOff := (dst.toNat + k * 8).toUSize
    let word := uget a srcOff hRead
    let a' := uset a dstOff word hWrite
    have hDst' : dst.toNat + nSlots.toNat * 8 ≤ a'.size := by rw [uset_size]; exact hDst
    have hSrc' : src.toNat + nSlots.toNat * 8 ≤ a'.size := by rw [uset_size]; exact hSrc
    by_cases hjk : j = k
    · subst j
      have hTail : dstOff.toNat + 8 ≤ dst.toNat + (k + 1) * 8 := by
        rw [hDstNat]
        omega
      have hOut := copyRow.go_outside dst src nSlots hDstFit hSrcFit (k + 1)
        (Nat.succ_le_of_lt hlt) a' hDst' hSrc' dstOff (by rw [uset_size]; exact hWrite)
        (Or.inl hTail)
      exact (uget_irrel _ _ _ _).trans (hOut.trans (uget_uset a dstOff word hWrite))
    · have hkj' : k + 1 ≤ j := by omega
      have hRec := copyRow.go_uget dst src nSlots hDstFit hSrcFit hsep (k + 1)
        (Nat.succ_le_of_lt hlt) a' hDst' hSrc' j hj hkj'
      let srcSlot := (src.toNat + j * 8).toUSize
      have hSrcSlotNat : srcSlot.toNat = src.toNat + j * 8 :=
        toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hSrcFit)
      have hSrcSlot : srcSlot.toNat + 8 ≤ a.size := by
        rw [hSrcSlotNat]; exact slotOff_le hj hSrc
      have hSepSlots : srcSlot.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + 8 ≤ srcSlot.toNat := by
        rw [hSrcSlotNat, hDstNat]
        cases hsep with
        | inl heq =>
          right
          rw [heq]
          omega
        | inr hrest =>
          cases hrest with
          | inl hbefore =>
            right
            omega
          | inr hafter =>
            left
            omega
      have hStable := uget_uset_disjoint a dstOff srcSlot word hWrite hSrcSlot hSepSlots
      exact (uget_irrel _ _ _ _).trans (hRec.trans hStable)
termination_by nSlots.toNat - k

/--
Destination slot `j` equals source slot `j` when the rows are the same or do not overlap.
-/
theorem copyRow_uget (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hsep : dst.toNat = src.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ src.toNat ∨
      src.toNat + nSlots.toNat * 8 ≤ dst.toNat)
    (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤
      (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size)
    (hSrcSlot : ((src.toNat + j * 8).toUSize).toNat + 8 ≤ a.size) :
    uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit) ((dst.toNat + j * 8).toUSize) hSlot =
      uget a ((src.toNat + j * 8).toUSize) hSrcSlot := by
  unfold copyRow
  exact (uget_irrel _ _ _ _).trans
    ((copyRow.go_uget dst src nSlots hDstFit hSrcFit hsep 0 (Nat.zero_le _) a hDst hSrc j hj
      (Nat.zero_le _)).trans (uget_irrel _ _ _ _))

/-- A slot that does not meet the destination row is unchanged. -/
theorem copyRow_uget_disjoint (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size) :
    uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit) off hSlot = uget a off hoff := by
  unfold copyRow
  exact (uget_irrel _ _ _ _).trans
    (copyRow.go_outside dst src nSlots hDstFit hSrcFit 0 (Nat.zero_le _) a hDst hSrc off hoff hdisj)

/-- Fill one row with `v`. Used to install an empty (`PosPlusOne.sentinel`) buffer. -/
def fillRow (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32) : ByteArray :=
  go 0 (Nat.zero_le _) a hDst
where
  go (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
      (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size) : ByteArray :=
    if hk' : k = nSlots.toNat then
      a
    else
      have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
      have hDstLt : dst.toNat + k * 8 < 2 ^ 32 := slotOff_lt hlt hDstFit
      let dstOff := (dst.toNat + k * 8).toUSize
      have hDstNat : dstOff.toNat = dst.toNat + k * 8 := toNat_toUSize_of_lt_2_pow_32 hDstLt
      have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le hlt hDst
      let a' := uset a dstOff v hWrite
      have hsize : a'.size = a.size := uset_size a dstOff v hWrite
      go (k + 1) (Nat.succ_le_of_lt hlt) a' (by rw [hsize]; exact hDst)
  termination_by nSlots.toNat - k

private theorem fillRow.go_size (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size) :
    (fillRow.go dst nSlots v hFit k hk a hDst).size = a.size := by
  unfold fillRow.go
  by_cases hk' : k = nSlots.toNat
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    exact (fillRow.go_size dst nSlots v hFit (k + 1)
      (Nat.succ_le_of_lt (Nat.lt_of_le_of_ne hk hk'))
      (uset a ((dst.toNat + k * 8).toUSize) v (by
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt (Nat.lt_of_le_of_ne hk hk') hFit)]
        exact slotOff_le (Nat.lt_of_le_of_ne hk hk') hDst))
      (by rw [uset_size]; exact hDst)).trans
      (uset_size _ _ _ _)
termination_by nSlots.toNat - k

/-- A slot disjoint from the not-yet-written suffix of the row is left unchanged. -/
private theorem fillRow.go_outside (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat + k * 8 ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat) :
    uget (fillRow.go dst nSlots v hFit k hk a hDst) off
        (by rw [fillRow.go_size dst nSlots v hFit k hk a hDst]; exact hoff) =
      uget a off hoff := by
  unfold fillRow.go
  by_cases hk' : k = nSlots.toNat
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
    have hDstNat : ((dst.toNat + k * 8).toUSize).toNat = dst.toNat + k * 8 :=
      toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hlt hFit)
    have hWrite : ((dst.toNat + k * 8).toUSize).toNat + 8 ≤ a.size := by
      rw [hDstNat]; exact slotOff_le hlt hDst
    let dstOff := (dst.toNat + k * 8).toUSize
    have hWriteDisj : off.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + 8 ≤ off.toNat := by
      cases hdisj with
      | inl hle =>
        rw [hDstNat]
        exact Or.inl hle
      | inr hge =>
        right
        rw [hDstNat]
        have hk1 : k + 1 ≤ nSlots.toNat := Nat.succ_le_of_lt hlt
        omega
    have hdisj' : off.toNat + 8 ≤ dst.toNat + (k + 1) * 8 ∨
        dst.toNat + nSlots.toNat * 8 ≤ off.toNat := by
      cases hdisj with
      | inl hle =>
        left
        omega
      | inr hge =>
        exact Or.inr hge
    have hRec := fillRow.go_outside dst nSlots v hFit (k + 1) (Nat.succ_le_of_lt hlt)
      (uset a dstOff v hWrite) (by rw [uset_size]; exact hDst) off
      (by rw [uset_size]; exact hoff) hdisj'
    have hKeep := uget_uset_disjoint a dstOff off v hWrite hoff hWriteDisj
    exact (uget_irrel _ _ _ _).trans (hRec.trans hKeep)
termination_by nSlots.toNat - k

/-- Slot `j` of the suffix that `go` still has to fill reads back as `v`. -/
private theorem fillRow.go_uget (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (j : Nat) (hj : j < nSlots.toNat) (hkj : k ≤ j) :
    uget (fillRow.go dst nSlots v hFit k hk a hDst) ((dst.toNat + j * 8).toUSize)
      (by
        rw [fillRow.go_size dst nSlots v hFit k hk a hDst]
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hFit)]
        exact slotOff_le hj hDst) = v := by
  unfold fillRow.go
  by_cases hk' : k = nSlots.toNat
  · simp only [hk'] at hkj
    omega
  · simp only [hk', ↓reduceDIte]
    have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
    have hDstNat : ((dst.toNat + k * 8).toUSize).toNat = dst.toNat + k * 8 :=
      toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hlt hFit)
    have hWrite : ((dst.toNat + k * 8).toUSize).toNat + 8 ≤ a.size := by
      rw [hDstNat]; exact slotOff_le hlt hDst
    let dstOff := (dst.toNat + k * 8).toUSize
    let a' := uset a dstOff v hWrite
    have hDst' : dst.toNat + nSlots.toNat * 8 ≤ a'.size := by rw [uset_size]; exact hDst
    by_cases hjk : j = k
    · subst j
      have hTail : dstOff.toNat + 8 ≤ dst.toNat + (k + 1) * 8 := by
        rw [hDstNat]
        omega
      have hOut := fillRow.go_outside dst nSlots v hFit (k + 1) (Nat.succ_le_of_lt hlt) a' hDst'
        dstOff (by rw [uset_size]; exact hWrite) (Or.inl hTail)
      exact (uget_irrel _ _ _ _).trans (hOut.trans (uget_uset a dstOff v hWrite))
    · have hRec := fillRow.go_uget dst nSlots v hFit (k + 1) (Nat.succ_le_of_lt hlt) a' hDst'
        j hj (by omega)
      exact (uget_irrel _ _ _ _).trans hRec
termination_by nSlots.toNat - k

/-- Every slot of a filled row reads back as `v`. -/
theorem fillRow_uget (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    uget (fillRow a dst nSlots v hDst hFit) ((dst.toNat + j * 8).toUSize) hSlot = v := by
  unfold fillRow
  exact (uget_irrel _ _ _ _).trans
    (fillRow.go_uget dst nSlots v hFit 0 (Nat.zero_le _) a hDst j hj (Nat.zero_le _))

/-- A slot that does not meet the filled row is unchanged. -/
theorem fillRow_uget_disjoint (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    uget (fillRow a dst nSlots v hDst hFit) off hSlot = uget a off hoff := by
  unfold fillRow
  exact (uget_irrel _ _ _ _).trans
    (fillRow.go_outside dst nSlots v hFit 0 (Nat.zero_le _) a hDst off hoff hdisj)

/-- Append `rows` zeroed rows. The caller overwrites them before they are read. -/
def growRows (a : ByteArray) (rows nSlots : Nat) : ByteArray :=
  go (rows * nSlots * 8) a
where
  go : Nat → ByteArray → ByteArray
    | 0, a => a
    | n + 1, a => go n (a.push 0)
  termination_by n => n

/-- Sentinel slot: `PosPlusOne.sentinel`. -/
@[inline]
def sentinelWord (s : String) : UInt64 :=
  (s.utf8ByteSize + 1).toUInt64

/-- Byte index of a valid position. -/
@[inline]
def encodePos {s : String} (p : Pos s) : UInt64 :=
  p.offset.byteIdx.toUInt64

/--
A capture word is either the sentinel (`utf8ByteSize + 1`) or the byte index of a
valid position. `NFA.WellFormed` does not state this: saves copy positions the VM
already holds.
-/
def SlotWord (s : String) (w : UInt64) : Prop :=
  w.toNat = s.utf8ByteSize + 1 ∨ ∃ p : Pos s, w.toNat = p.offset.byteIdx

theorem SlotWord.sentinel {s : String} (h : s.utf8ByteSize + 1 < 2 ^ 64) :
    SlotWord s (sentinelWord s) := by
  refine Or.inl ?_
  unfold sentinelWord
  rw [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa using h)

theorem SlotWord.encode {s : String} (p : Pos s) (h : p.offset.byteIdx < 2 ^ 64) :
    SlotWord s (encodePos p) := by
  refine Or.inr ⟨p, ?_⟩
  unfold encodePos
  rw [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa using h)

theorem fillRow_slotWord {s : String} (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hv : SlotWord s v) (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    SlotWord s (uget (fillRow a dst nSlots v hDst hFit) ((dst.toNat + j * 8).toUSize) hSlot) := by
  rw [fillRow_uget a dst nSlots v hDst hFit j hj hSlot]
  exact hv

theorem fillRow_slotWord_disjoint {s : String} (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a off hoff))
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    SlotWord s (uget (fillRow a dst nSlots v hDst hFit) off hSlot) := by
  rw [fillRow_uget_disjoint a dst nSlots v hDst hFit off hoff hdisj hSlot]
  exact hw

theorem copyRow_slotWord {s : String} (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hsep : dst.toNat = src.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ src.toNat ∨
      src.toNat + nSlots.toNat * 8 ≤ dst.toNat)
    (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤
      (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size)
    (hSrcSlot : ((src.toNat + j * 8).toUSize).toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a ((src.toNat + j * 8).toUSize) hSrcSlot)) :
    SlotWord s (uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit)
      ((dst.toNat + j * 8).toUSize) hSlot) := by
  rw [copyRow_uget a dst src nSlots hDst hSrc hDstFit hSrcFit hsep j hj hSlot hSrcSlot]
  exact hw

theorem copyRow_slotWord_disjoint {s : String} (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a off hoff))
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size) :
    SlotWord s (uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit) off hSlot) := by
  rw [copyRow_uget_disjoint a dst src nSlots hDst hSrc hDstFit hSrcFit off hoff hdisj hSlot]
  exact hw

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
