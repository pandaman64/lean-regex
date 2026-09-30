module

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

def ClassTable.compile (cs : Classes) : ClassTable :=
  let runs := runsOf cs
  let high := highRuns runs
  let (b0, b1, b2, b3) := packBits runs
  { b0, b1, b2, b3
    nHigh := high.size.toUInt32
    high := packRuns high }

@[inline]
private unsafe def bitmapMem (t : ClassTable) (c : UInt32) : Bool :=
  let word := c >>> 6
  let bit := (c &&& 63).toUInt64
  let w :=
    if word == 0 then t.b0
    else if word == 1 then t.b1
    else if word == 2 then t.b2
    else t.b3
  ((w >>> bit) &&& 1) == 1

@[inline]
private unsafe def linearMem (runs : ByteArray) (n c : UInt32) : Bool :=
  let rec go (i : UInt32) : Bool :=
    if i < n then
      let off := i.toUSize * 8
      let lo := runs.ugetUInt32LE off lcProof
      let hi := runs.ugetUInt32LE (off + 4) lcProof
      if c < lo then
        false
      else if c ≤ hi then
        true
      else
        go (i + 1)
    else
      false
  go 0

/-- Bitmap below 256, then a linear scan of the high runs. -/
@[inline]
unsafe def ClassTable.contains (t : ClassTable) (c : Char) : Bool :=
  let v := c.val
  if v < 256 then bitmapMem t v else linearMem t.high t.nHigh v

end Regex.VM.ClassTable

end
