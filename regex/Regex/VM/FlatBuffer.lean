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

/-- Eight bytes per capture slot. -/
abbrev slotBytes : USize := 8

/-- Byte offset of row `row` when each row holds `nSlots` slots. -/
@[inline]
def rowOff (row nSlots : USize) : USize :=
  row * nSlots * slotBytes

@[inline]
def uget (a : ByteArray) (off : USize) (h : off.toNat + 8 ≤ a.size) : UInt64 :=
  a.ugetUInt64LE off h

@[inline]
def uset (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) : ByteArray :=
  a.usetUInt64LE off v h

theorem uset_size (a : ByteArray) (off : USize) (v : UInt64) (h : off.toNat + 8 ≤ a.size) :
    (uset a off v h).size = a.size := by
  simp [uset, ByteArray.usetUInt64LE_size]

/-- This build's `USize` is 64 bits. The same fact is used by `ClassTable`. -/
private theorem usize_eq_two_pow_64 : USize.size = 2 ^ 64 := by
  native_decide

private theorem two_pow_numBits_eq : 2 ^ System.Platform.numBits = 2 ^ 64 := by
  rw [← USize.size_eq_two_pow, usize_eq_two_pow_64]

private theorem toNat_toUSize_of_lt {n : Nat} (h : n < 2 ^ 64) : n.toUSize.toNat = n := by
  rw [Nat.toUSize, USize.toNat_ofNat']
  apply Nat.mod_eq_of_lt
  rw [two_pow_numBits_eq]
  exact h

private theorem slotOff_lt {base count k : Nat} (hk : k < count) (hfit : base + count * 8 ≤ 2 ^ 64) :
    base + k * 8 < 2 ^ 64 := by
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
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 64)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 64) : ByteArray :=
  let rec go (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
      (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
      (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size) : ByteArray :=
    if hk' : k = nSlots.toNat then
      a
    else
      have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
      have hSrcLt : src.toNat + k * 8 < 2 ^ 64 := slotOff_lt hlt hSrcFit
      have hDstLt : dst.toNat + k * 8 < 2 ^ 64 := slotOff_lt hlt hDstFit
      let srcOff := (src.toNat + k * 8).toUSize
      let dstOff := (dst.toNat + k * 8).toUSize
      have hSrcNat : srcOff.toNat = src.toNat + k * 8 := toNat_toUSize_of_lt hSrcLt
      have hDstNat : dstOff.toNat = dst.toNat + k * 8 := toNat_toUSize_of_lt hDstLt
      have hRead : srcOff.toNat + 8 ≤ a.size := by rw [hSrcNat]; exact slotOff_le hlt hSrc
      have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le hlt hDst
      let a' := uset a dstOff (uget a srcOff hRead) hWrite
      have hsize : a'.size = a.size := uset_size a dstOff _ hWrite
      go (k + 1) (Nat.succ_le_of_lt hlt) a' (by rw [hsize]; exact hDst) (by rw [hsize]; exact hSrc)
  termination_by nSlots.toNat - k
  go 0 (Nat.zero_le _) a hDst hSrc

/-- Fill one row with `v`. Used to install an empty (`PosPlusOne.sentinel`) buffer. -/
def fillRow (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 64) : ByteArray :=
  let rec go (k : Nat) (hk : k ≤ nSlots.toNat) (a : ByteArray)
      (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size) : ByteArray :=
    if hk' : k = nSlots.toNat then
      a
    else
      have hlt : k < nSlots.toNat := Nat.lt_of_le_of_ne hk hk'
      have hDstLt : dst.toNat + k * 8 < 2 ^ 64 := slotOff_lt hlt hDstFit
      let dstOff := (dst.toNat + k * 8).toUSize
      have hDstNat : dstOff.toNat = dst.toNat + k * 8 := toNat_toUSize_of_lt hDstLt
      have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le hlt hDst
      let a' := uset a dstOff v hWrite
      have hsize : a'.size = a.size := uset_size a dstOff v hWrite
      go (k + 1) (Nat.succ_le_of_lt hlt) a' (by rw [hsize]; exact hDst)
  termination_by nSlots.toNat - k
  go 0 (Nat.zero_le _) a hDst

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
Decode one slot.

A word equal to `sentinelWord` is `PosPlusOne.sentinel`. Any other word was
written by `encodePos` from a valid position.
-/
@[inline]
unsafe def decode {s : String} (w : UInt64) : PosPlusOne s :=
  if w.toNat == s.utf8ByteSize + 1 then
    .sentinel s
  else
    .pos ⟨⟨w.toNat⟩, lcProof⟩

/-- Row 0 as a `Vector` of positions. One allocation, at the API boundary. -/
unsafe def toBuffer {s : String} (a : ByteArray) (nSlots : Nat) : Vector (PosPlusOne s) nSlots :=
  Vector.ofFn fun i : Fin nSlots =>
    decode (uget a (i.val.toUSize * slotBytes) lcProof)

end Regex.VM.FlatBuffer

end
