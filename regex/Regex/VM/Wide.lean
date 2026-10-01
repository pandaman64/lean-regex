module

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
def WordArray.size (a : WordArray) : Nat :=
  a.data.size / 4

def WordArray.push (a : WordArray) (v : UInt32) : WordArray :=
  ⟨a.data.push v.toUInt8
      |>.push (v >>> 8).toUInt8
      |>.push (v >>> 16).toUInt8
      |>.push (v >>> 24).toUInt8⟩

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

end Regex.VM.Wide

end
