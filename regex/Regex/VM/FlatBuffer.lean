module

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

/-- Copy `nSlots` slots from byte offset `src` onto `dst`. -/
@[inline]
unsafe def copyRow (a : ByteArray) (dst src nSlots : USize) : ByteArray :=
  let rec go (k : USize) (a : ByteArray) : ByteArray :=
    if k == nSlots then
      a
    else
      let v := uget a (src + k * slotBytes) lcProof
      go (k + 1) (uset a (dst + k * slotBytes) v lcProof)
  go 0 a

/-- Fill one row with `v`. Used to install an empty (`PosPlusOne.sentinel`) buffer. -/
@[inline]
unsafe def fillRow (a : ByteArray) (dst nSlots : USize) (v : UInt64) : ByteArray :=
  let rec go (k : USize) (a : ByteArray) : ByteArray :=
    if k == nSlots then
      a
    else
      go (k + 1) (uset a (dst + k * slotBytes) v lcProof)
  go 0 a

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
