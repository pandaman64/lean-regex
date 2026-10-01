module

public import Init.Data.ByteArray.Lemmas
public import Init.Data.UInt.Lemmas
public import Regex.Data.Classes
public import Regex.VM.Wide

open Regex.Data (Classes Class PerlClass PerlClassKind)

/-!
Compiled character-class tables for the refined PikeVM.

`Classes` stays the specification: complement, intersection, difference, and
symmetric difference are evaluated here, once, into a sorted list of inclusive
code-point runs. The match loop never dispatches on those operators.

A Latin-1 bitmap answers `U+0000`–`U+00FF`. Code points at or above 256 are a
linear scan of the same runs, clipped so each lower endpoint is at least 256.
An empty high list means the character is not in the set.
-/

public section

namespace Regex.VM.ClassTable

open Regex.VM.Wide (lt_two_pow_numBits_of_lt_2_pow_32 toNat_uSize_ofNat_of_lt)

private def univHi : UInt32 := 0x10FFFF

/-- Insert `[lo, hi]` into a sorted, disjoint, non-adjacent run list. -/
private def pushMerge (acc : Array (UInt32 × UInt32)) (lo hi : UInt32) :
    Array (UInt32 × UInt32) :=
  if h0 : acc.size = 0 then
    acc.push (lo, hi)
  else
    let last := acc.size - 1
    have hlt : last < acc.size := by omega
    let (a, b) := acc[last]
    if b < univHi && b + 1 < lo then
      acc.push (lo, hi)
    else
      acc.set last (a, if b < hi then hi else b)

private def unionRuns (a b : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  let rec go (i j : Nat) (acc : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
    if hi : i < a.size then
      if hj : j < b.size then
        let (x0, x1) := a[i]
        let (y0, y1) := b[j]
        if x0 ≤ y0 then
          go (i + 1) j (pushMerge acc x0 x1)
        else
          go i (j + 1) (pushMerge acc y0 y1)
      else
        finish a i acc
    else
      finish b j acc
  termination_by (a.size - i) + (b.size - j)
  go 0 0 #[]
where
  finish (src : Array (UInt32 × UInt32)) (k : Nat) (acc : Array (UInt32 × UInt32)) :
      Array (UInt32 × UInt32) :=
    if hk : k < src.size then
      let (lo, hi) := src[k]
      finish src (k + 1) (pushMerge acc lo hi)
    else
      acc
  termination_by src.size - k

private def interRuns (a b : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  let rec go (i j : Nat) (acc : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
    if hi : i < a.size then
      if hj : j < b.size then
        let (a0, a1) := a[i]
        let (b0, b1) := b[j]
        let lo := max a0 b0
        let hiR := min a1 b1
        let acc := if lo ≤ hiR then pushMerge acc lo hiR else acc
        if a1 < b1 then go (i + 1) j acc else go i (j + 1) acc
      else
        acc
    else
      acc
  termination_by (a.size - i) + (b.size - j)
  go 0 0 #[]

/-- Remove `[cutLo, cutHi]` from one inclusive run. -/
private def clipRun (lo hi cutLo cutHi : UInt32) : Array (UInt32 × UInt32) :=
  if hi < cutLo || cutHi < lo then
    #[(lo, hi)]
  else
    let left := if lo < cutLo then #[(lo, cutLo - 1)] else #[]
    let right := if cutHi < hi then #[(cutHi + 1, hi)] else #[]
    left ++ right

private def diffRuns (a b : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  b.foldl (init := a) fun acc (cutLo, cutHi) =>
    acc.foldl (init := #[]) fun out (lo, hi) =>
      out ++ clipRun lo hi cutLo cutHi

/-- Complement against Unicode scalar values that fit in `U+0000`–`U+10FFFF`.
Surrogates are never tested: a string `Char` is not one. -/
private def complementRuns (runs : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  let rec go (i : Nat) (next : UInt32) (acc : Array (UInt32 × UInt32)) :
      Array (UInt32 × UInt32) :=
    if h : i < runs.size then
      let (lo, hi) := runs[i]
      let acc := if next < lo then acc.push (next, lo - 1) else acc
      go (i + 1) (hi + 1) acc
    else if next ≤ univHi then
      acc.push (next, univHi)
    else
      acc
  termination_by runs.size - i
  go 0 0 #[]

private def kindRuns : PerlClassKind → Array (UInt32 × UInt32)
  | .digit => #[(48, 57)]
  | .space => #[(9, 10), (12, 13), (32, 32)]
  | .word => #[(48, 57), (65, 90), (95, 95), (97, 122)]

private def perlRuns (pc : PerlClass) : Array (UInt32 × UInt32) :=
  if pc.negated then complementRuns (kindRuns pc.kind) else kindRuns pc.kind

/-- Every operator becomes run-list algebra. The match loop does not see them. -/
private def runsOf : Classes → Array (UInt32 × UInt32)
  | .atom (.single c) => #[(c.val, c.val)]
  | .atom (.range a b) => if a.val ≤ b.val then #[(a.val, b.val)] else #[]
  | .atom (.perl pc) => perlRuns pc
  | .complement e => complementRuns (runsOf e)
  | .union a b => unionRuns (runsOf a) (runsOf b)
  | .intersection a b => interRuns (runsOf a) (runsOf b)
  | .difference a b => diffRuns (runsOf a) (runsOf b)
  | .symDiff a b => unionRuns (diffRuns (runsOf a) (runsOf b)) (diffRuns (runsOf b) (runsOf a))

private def packRuns (runs : Array (UInt32 × UInt32)) : ByteArray :=
  runs.foldl (init := ByteArray.empty) fun bytes (lo, hi) =>
    bytes.push lo.toUInt8
      |>.push (lo >>> 8).toUInt8
      |>.push (lo >>> 16).toUInt8
      |>.push (lo >>> 24).toUInt8
      |>.push hi.toUInt8
      |>.push (hi >>> 8).toUInt8
      |>.push (hi >>> 16).toUInt8
      |>.push (hi >>> 24).toUInt8

private theorem packRuns_size (runs : Array (UInt32 × UInt32)) :
    (packRuns runs).size = runs.size * 8 := by
  unfold packRuns
  refine Array.foldl_induction (fun i (bytes : ByteArray) => bytes.size = i * 8) ?h0 ?hf
  case h0 => simp [ByteArray.size_empty]
  case hf =>
    intro i bytes ih
    simp only [ByteArray.size_push, ih]
    omega

/-- Runs that can match a code point ≥ 256. Lower endpoints are clipped. -/
private def highRuns (runs : Array (UInt32 × UInt32)) : Array (UInt32 × UInt32) :=
  runs.foldl (init := #[]) fun acc (lo, hi) =>
    if hi < 256 then
      acc
    else if lo < 256 then
      pushMerge acc 256 hi
    else
      pushMerge acc lo hi

private def packBits (runs : Array (UInt32 × UInt32)) : UInt64 × UInt64 × UInt64 × UInt64 :=
  let rec go (i : Nat) (w0 w1 w2 w3 : UInt64) : UInt64 × UInt64 × UInt64 × UInt64 :=
    if i < 256 then
      let c : UInt32 := i.toUInt32
      let hit := runs.any fun (lo, hi) => lo ≤ c && c ≤ hi
      if hit then
        let bit : UInt64 := 1 <<< (i % 64).toUInt64
        match i / 64 with
        | 0 => go (i + 1) (w0 ||| bit) w1 w2 w3
        | 1 => go (i + 1) w0 (w1 ||| bit) w2 w3
        | 2 => go (i + 1) w0 w1 (w2 ||| bit) w3
        | _ => go (i + 1) w0 w1 w2 (w3 ||| bit)
      else
        go (i + 1) w0 w1 w2 w3
    else
      (w0, w1, w2, w3)
  termination_by 256 - i
  go 0 0 0 0 0

/-- Bitmap words for `U+0000`–`U+00FF`, plus runs at or above 256. -/
structure ClassTable where
  b0 : UInt64
  b1 : UInt64
  b2 : UInt64
  b3 : UInt64
  /-- Number of high runs. Stored so the probe does not recompute it from the byte size. -/
  nHigh : UInt32
  high : ByteArray
  /-- The `nHigh` packed runs occupy `8 * nHigh` bytes at the front of `high`. -/
  packed : nHigh.toNat * 8 ≤ high.size
  /-- Those bytes fit in a 32-bit offset, so `USize` index arithmetic does not wrap. -/
  fits : nHigh.toNat * 8 < 2 ^ 32

/-- `i.toNat * 8 < 2^32`, so scaling the run index by 8 does not wrap `USize`. -/
private theorem toNat_u32_mul8 {i : UInt32} (h : i.toNat * 8 < 2 ^ 32) :
    (i.toUSize * 8).toNat = i.toNat * 8 := by
  rw [USize.toNat_mul, UInt32.toNat_toUSize, toNat_uSize_ofNat_of_lt 8 (by decide)]
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

private theorem toNat_uSize_add (off : USize) (k : Nat) (hk : k < 2 ^ 32) (h : off.toNat + k < 2 ^ 32) :
    (off + OfNat.ofNat k).toNat = off.toNat + k := by
  rw [USize.toNat_add, toNat_uSize_ofNat_of_lt k hk]
  exact Nat.mod_eq_of_lt (lt_two_pow_numBits_of_lt_2_pow_32 h)

private theorem toNat_add_one_of_lt {i n : UInt32} (h : i < n) : (i + 1).toNat = i.toNat + 1 := by
  have hlt : i.toNat < n.toNat := (UInt32.lt_iff_toNat_lt).mp h
  have hone : (1 : UInt32).toNat = 1 := by rw [UInt32.toNat_ofNat]
  rw [UInt32.toNat_add, hone]
  apply Nat.mod_eq_of_lt
  have := UInt32.toNat_lt n
  omega

/--
Compile `cs` to a bitmap plus packed high runs.

Returns `none` when the high-run table does not fit in a 32-bit byte offset.
Each run is 8 bytes, so that is `high.size < 2^29`.
-/
def ClassTable.compile (cs : Classes) : Option ClassTable :=
  let runs := runsOf cs
  let high := highRuns runs
  if hsz : high.size < 2 ^ 29 then
    let (b0, b1, b2, b3) := packBits runs
    let bytes := packRuns high
    have hn : high.size.toUInt32.toNat = high.size := by
      have h32 : high.size < UInt32.size := by
        have : high.size < 2 ^ 32 := by omega
        simpa [UInt32.size] using this
      rw [Nat.toUInt32_eq]
      simp [UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by simpa [UInt32.size] using h32)]
    have hpack : high.size.toUInt32.toNat * 8 ≤ bytes.size := by
      rw [hn, packRuns_size]
      exact Nat.le_refl _
    have hfits : high.size.toUInt32.toNat * 8 < 2 ^ 32 := by
      rw [hn]
      omega
    some ⟨b0, b1, b2, b3, high.size.toUInt32, bytes, hpack, hfits⟩
  else
    none

@[inline]
private def bitmapMem (t : ClassTable) (c : UInt32) : Bool :=
  let word := c >>> 6
  let bit := (c &&& 63).toUInt64
  let w :=
    if word == 0 then t.b0
    else if word == 1 then t.b1
    else if word == 2 then t.b2
    else t.b3
  ((w >>> bit) &&& 1) == 1

/--
Linear scan of packed `[lo, hi]` runs.

`@[inline]` exports the erased-proof specialization. The function is recursive, so
it is not inlined into the match loop; callers are rewritten to that specialization,
which takes only `runs`, `n`, `c`, and `i`.
-/
@[inline]
def linearScan (runs : ByteArray) (n c i : UInt32)
    (hpack : n.toNat * 8 ≤ runs.size) (hfits : n.toNat * 8 < 2 ^ 32) : Bool :=
  if hik : i < n then
    let off := i.toUSize * 8
    have hlt : i.toNat < n.toNat := (UInt32.lt_iff_toNat_lt).mp hik
    have hmul : i.toNat * 8 + 8 < 2 ^ 32 := by omega
    have hoff : off.toNat = i.toNat * 8 := toNat_u32_mul8 (by omega)
    have hspan : i.toNat * 8 + 8 ≤ runs.size := by omega
    have hlo : off.toNat + 4 ≤ runs.size := by omega
    have hadd : (off + 4).toNat = off.toNat + 4 := by
      apply toNat_uSize_add off 4 (by decide)
      rw [hoff]
      omega
    have hhi : (off + 4).toNat + 4 ≤ runs.size := by omega
    let lo := runs.ugetUInt32LE off hlo
    let hi := runs.ugetUInt32LE (off + 4) hhi
    if c < lo then
      false
    else if c ≤ hi then
      true
    else
      linearScan runs n c (i + 1) hpack hfits
  else
    false
termination_by n.toNat - i.toNat
decreasing_by
  rw [toNat_add_one_of_lt hik]
  exact Nat.sub_succ_lt_self n.toNat i.toNat ((UInt32.lt_iff_toNat_lt).mp hik)

@[inline]
private def linearMem (runs : ByteArray) (n c : UInt32)
    (hpack : n.toNat * 8 ≤ runs.size) (hfits : n.toNat * 8 < 2 ^ 32) : Bool :=
  linearScan runs n c 0 hpack hfits

/-- Bitmap below 256, then a linear scan of the high runs. -/
@[inline]
def ClassTable.contains (t : ClassTable) (c : Char) : Bool :=
  let v := c.val
  if v < 256 then bitmapMem t v else linearMem t.high t.nHigh v t.packed t.fits

end Regex.VM.ClassTable

end
