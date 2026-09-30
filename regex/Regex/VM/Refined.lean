module

public import Regex.Data.Anchor
public import Regex.Data.Classes
public import Regex.Data.String
public import Regex.NFA.Basic
public import Regex.Regex.Basic
public import Regex.Regex.OptimizationInfo
public import Regex.Regex.Utilities
public import Regex.Strategy
public import Regex.VM.ClassTable
public import Regex.VM.FlatBuffer
public import Regex.VM.Wide

open Regex.Data (Anchor)
open Regex.VM.ClassTable (ClassTable)
open Regex.VM.FlatBuffer
open Regex.VM.Wide (WordArray)
open String (Pos PosPlusOne Slice)

/-!
Refined PikeVM.

The stock VM loads each NFA state as a boxed `NFA.Node` and pushes ε-work onto a `List`.
This module keeps the same Thompson NFA and the same left-biased PikeVM schedule, but stores
states in a flat scalar buffer and the ε-stack in reusable arrays so the hot loop does not
allocate a node, a cons cell, or a search-state wrapper.

`WordArray` (`Regex.VM.Wide`) is a one-field wrapper around a `ByteArray`. Lean erases that
wrapper, and each `UInt32` occupies four raw bytes. An `Array UInt32` would not: `Array` is
polymorphic, so every slot is a `lean_object*` and each `UInt32` is passed through
`lean_box_uint32`. Loads and stores go through `ByteArray.ugetUInt32LE` /
`usetUInt32LE`, the wide reader adapted from lean-zip. Each state is three contiguous words
(tag, next, extra), twelve bytes from a single base offset. Sparse-set state ids and the
ε-stack of state ids use the same buffer. Capture slots use `FlatBuffer`, an
unboxed `ByteArray` of `UInt64` byte offsets, instead of `BufferStrategy`'s
`Array` of `Vector`s. The hot loop is hard-coded to that layout: a save writes
one word into a preallocated row and does not allocate a capture buffer.
-/

public section

namespace Regex.VM.Refined

/-- Node kinds packed into the first word of each state. `abbrev` so compares fold to immediates. -/
abbrev tagDone : UInt32 := 0
abbrev tagFail : UInt32 := 1
abbrev tagEpsilon : UInt32 := 2
abbrev tagAnchor : UInt32 := 3
abbrev tagChar : UInt32 := 4
abbrev tagSplit : UInt32 := 5
abbrev tagSave : UInt32 := 6
abbrev tagSparse : UInt32 := 7

/-- Twelve bytes per state: tag, next, extra, each a little-endian `UInt32`. -/
abbrev strideBytes : USize := 12

/-- Flat NFA. `classes` holds one compiled table per `.sparse` state. -/
structure FlatNFA where
  words : WordArray
  classes : Array ClassTable
  size : UInt32
  start : UInt32

def anchorKind : Anchor → UInt32
  | .start => 0
  | .eos => 1
  | .wordBoundary => 2
  | .nonWordBoundary => 3

def encode (classes : Array ClassTable) : NFA.Node → Option (UInt32 × UInt32 × UInt32 × Array ClassTable)
  | .done => some (tagDone, 0, 0, classes)
  | .fail => some (tagFail, 0, 0, classes)
  | .epsilon next => some (tagEpsilon, next.toUInt32, 0, classes)
  | .anchor a next => some (tagAnchor, next.toUInt32, anchorKind a, classes)
  | .char c next => some (tagChar, next.toUInt32, c.val, classes)
  | .split next₁ next₂ => some (tagSplit, next₁.toUInt32, next₂.toUInt32, classes)
  | .save offset next =>
    if offset < UInt32.size then
      some (tagSave, next.toUInt32, offset.toUInt32, classes)
    else
      none
  | .sparse cs next =>
    if classes.size < UInt32.size then
      some (tagSparse, next.toUInt32, classes.size.toUInt32, classes.push (ClassTable.compile cs))
    else
      none

/--
Translate `nfa` into the flat buffer.

Returns `none` when a state index or a save slot does not fit in `UInt32` (the packed word
width). Compiled expressions used by the benchmark fit comfortably.
-/
def ofNFA (nfa : NFA) : Option FlatNFA :=
  if nfa.size = 0 || nfa.size ≥ UInt32.size then
    none
  else
    go 0 (WordArray.emptyWithCapacity (nfa.size * 3)) #[]
where
  go (i : Nat) (words : WordArray) (classes : Array ClassTable) : Option FlatNFA :=
    if h : i < nfa.nodes.size then
      match encode classes nfa.nodes[i] with
      | none => none
      | some (tag, next, extra, classes') =>
        go (i + 1) (words.push tag |>.push next |>.push extra) classes'
    else
      some {
        words
        classes
        size := nfa.size.toUInt32
        start := nfa.start.toUInt32
      }
  termination_by nfa.nodes.size - i

@[inline]
def anchorOf (k : UInt32) : Anchor :=
  if k == 0 then .start
  else if k == 1 then .eos
  else if k == 2 then .wordBoundary
  else .nonWordBoundary

@[inline]
def anchorTest {s : String} (k : UInt32) (p : Pos s) : Bool :=
  (anchorOf k).test p

/-- After this closure, the filled next-buffer becomes current and stepping starts. -/
abbrev phaseClosure : UInt32 := 0
/-- Closure started by a character transition. `i` is the state index to resume. -/
abbrev phaseStepClosure : UInt32 := 1
/-- Walk the current sparse set and take character transitions. -/
abbrev phaseStep : UInt32 := 2

/-- Updates are stored only for states that `stepChar` may read, matching the stock VM. -/
@[inline]
def writesUpdate (tag : UInt32) : Bool :=
  tag == tagDone || tag == tagChar || tag == tagSparse

/--
Reusable sparse-set, ε-stack, and capture-slot buffers.

`caps` is one flat capture buffer (`FlatBuffer`). Row 0 holds the accepted
match, row 1 the closure match, then `nStates` rows for the set being read,
`nStates` rows for the set being written, and `stkS.size` stack rows. Counts
are not stored: each search starts them at zero, which is the usual sparse-set
clear. Capture rows are overwritten before they are read, so the block is not
refilled per match.
-/
structure Scratch where
  cDen : WordArray
  cSpa : WordArray
  nDen : WordArray
  nSpa : WordArray
  stkS : WordArray
  caps : ByteArray
  nSlots : Nat
  nStates : UInt32

def Scratch.mkFor (nStates nSlots : Nat) : Scratch :=
  let cap := max (nStates * 4) 8
  {
    cDen := WordArray.zeros nStates
    cSpa := WordArray.zeros nStates
    nDen := WordArray.zeros nStates
    nSpa := WordArray.zeros nStates
    stkS := WordArray.zeros cap
    caps := ByteArray.zero ((2 + 2 * nStates + cap) * nSlots * 8).toUSize
    nSlots
    nStates := nStates.toUInt32
  }

structure SearchRun where
  matched : Bool
  scratch : Scratch

@[inline]
def SearchRun.pack (matched : Bool) (nSlots : Nat) (nStates : UInt32)
    (cDen cSpa nDen nSpa stkS : WordArray) (caps : ByteArray) : SearchRun :=
  { matched, scratch := { cDen, cSpa, nDen, nSpa, stkS, caps, nSlots, nStates } }

/--
Tail-recursive PikeVM. Every recursive call is in tail position so the buffers stay unique.
`c*` is the set being read, `n*` the set being written. Capture slots live in `caps`; `cRow0`
and `nRow0` are the first rows of those two sets and are swapped, not copied, when a closure
finishes. `clos` means row 1 holds the match found by the closure in progress; `matched` means
row 0 holds the match already accepted.

`p` is the position of the active `eachStepChar` loop. `cp` is the position of the closure
(where saves and anchors run). They differ only while a character transition's closure is in
progress: the remaining states of this character must still be tested at `p` if that closure
does not reach `.done`.
-/
unsafe def eval {s : String}
    (words : WordArray) (classes : Array ClassTable) (start : UInt32)
    (nSlots : Nat) (nStates : UInt32) (slots : USize) (sent : UInt64)
    (cRow0 nRow0 stackRow0 : USize)
    (p cp : Pos s) (matched clos : Bool)
    (cCount : UInt32) (cDen cSpa : WordArray)
    (nCount : UInt32) (nDen nSpa : WordArray)
    (stkS : WordArray) (caps : ByteArray) (sp : Nat)
    (phase i : UInt32) : SearchRun :=
  if phase == phaseStep then
    if hp : p = s.endPos then
      SearchRun.pack matched nSlots nStates cDen cSpa nDen nSpa stkS caps
    else if i == 0 && cCount == 0 && matched then
      SearchRun.pack matched nSlots nStates cDen cSpa nDen nSpa stkS caps
    else if i == cCount then
      if !matched then
        let caps := fillRow caps (rowOff stackRow0 slots) slots sent
        let stkS := stkS.usetWord 0 start
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          (p.next hp) (p.next hp) false false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps 1
          phaseClosure 0
      else
        eval words classes start nSlots nStates slots sent nRow0 cRow0 stackRow0
          (p.next hp) (p.next hp) matched false
          nCount nDen nSpa
          (0 : UInt32) cDen cSpa
          stkS caps 0
          phaseStep 0
    else
      let state := cDen.ugetWord i.toUSize
      let base := state.toUSize * strideBytes
      let tag := words.uget base
      if tag == tagDone then
        -- Lower-priority threads lose to the `.done` state already in this set.
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep cCount
      else if tag == tagChar then
        let extra := words.uget (base + 8)
        if (p.get hp).val == extra then
          let nextW := words.uget (base + 4)
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots
          let stkS := stkS.usetWord 0 nextW
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p (p.next hp) matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps 1
            phaseStepClosure i
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p p matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp
            phaseStep (i + 1)
      else if tag == tagSparse then
        let extra := words.uget (base + 8)
        let cs := classes.uget extra.toUSize lcProof
        if cs.contains (p.get hp) then
          let nextW := words.uget (base + 4)
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots
          let stkS := stkS.usetWord 0 nextW
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p (p.next hp) matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps 1
            phaseStepClosure i
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p p matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp
            phaseStep (i + 1)
      else
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep (i + 1)
  else if sp == 0 then
    -- `phaseClosure` always installs the closure result and steps at `cp`. A step-closure does
    -- too when it reached `.done`; otherwise the rest of this character is tested at `p`.
    if phase == phaseClosure || clos then
      let caps :=
        if clos then copyRow caps (rowOff 0 slots) (rowOff 1 slots) slots else caps
      eval words classes start nSlots nStates slots sent nRow0 cRow0 stackRow0
        cp cp clos false
        nCount nDen nSpa
        (0 : UInt32) cDen cSpa
        stkS caps 0
        phaseStep 0
    else
      eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
        p p matched false
        cCount cDen cSpa
        nCount nDen nSpa
        stkS caps 0
        phaseStep (i + 1)
  else
    let sp' := sp - 1
    let stkOff := rowOff (stackRow0 + sp'.toUSize) slots
    let state := stkS.ugetWord sp'.toUSize
    let si := nSpa.ugetWord state.toUSize
    let seen := if si < nCount then nDen.ugetWord si.toUSize == state else false
    if seen then
      eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
        p cp matched clos
        cCount cDen cSpa
        nCount nDen nSpa
        stkS caps sp'
        phase i
    else
      let base := state.toUSize * strideBytes
      let tag := words.uget base
      let nextW := words.uget (base + 4)
      let extra := words.uget (base + 8)
      -- First `.done` wins. Copy into row 1 before any later save mutates this stack row.
      let caps :=
        if tag == tagDone && !clos then
          copyRow caps (rowOff 1 slots) stkOff slots
        else
          caps
      let clos := tag == tagDone || clos
      let caps :=
        if writesUpdate tag then
          copyRow caps (rowOff (nRow0 + state.toUSize) slots) stkOff slots
        else
          caps
      let nDen := nDen.usetWord nCount.toUSize state
      let nSpa := nSpa.usetWord state.toUSize nCount
      let nCount := nCount + 1
      -- Two free slots cover a `.split` (next₂ under next₁, so next₁ is popped first).
      let grew := sp' + 2 > stkS.size
      let caps := if grew then growRows caps 2 nSlots else caps
      let stkS := if grew then stkS.push 0 |>.push 0 else stkS
      if tag == tagEpsilon then
        let stkS := stkS.usetWord sp'.toUSize nextW
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps (sp' + 1)
          phase i
      else if tag == tagSplit then
        -- The two branches must not share one mutable row.
        let caps := copyRow caps (rowOff (stackRow0 + (sp' + 1).toUSize) slots) stkOff slots
        let stkS := stkS.usetWord sp'.toUSize extra
        let stkS := stkS.usetWord (sp' + 1).toUSize nextW
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps (sp' + 2)
          phase i
      else if tag == tagSave then
        -- `setIfInBounds`: a save past the buffer leaves the row unchanged.
        let caps :=
          if extra.toNat < nSlots then
            uset caps (stkOff + extra.toUSize * slotBytes) (encodePos cp)
          else
            caps
        let stkS := stkS.usetWord sp'.toUSize nextW
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps (sp' + 1)
          phase i
      else if tag == tagAnchor then
        if anchorTest extra cp then
          let stkS := stkS.usetWord sp'.toUSize nextW
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p cp matched clos
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps (sp' + 1)
            phase i
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p cp matched clos
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp'
            phase i
      else
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp'
          phase i

unsafe def search {s : String} (nfa : FlatNFA) (scratch : Scratch) (sent : UInt64) (p : Pos s) :
    SearchRun :=
  if nfa.size == 0 then
    { matched := false, scratch }
  else
    let words := nfa.words
    let classes := nfa.classes
    let start := nfa.start
    let { cDen, cSpa, nDen, nSpa, stkS, caps, nSlots, nStates } := scratch
    let slots := nSlots.toUSize
    let cRow0 : USize := 2
    let nRow0 : USize := 2 + nStates.toUSize
    let stackRow0 : USize := nRow0 + nStates.toUSize
    let caps := fillRow caps (rowOff stackRow0 slots) slots sent
    let stkS := stkS.usetWord 0 start
    eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
      p p false false
      (0 : UInt32) cDen cSpa
      (0 : UInt32) nDen nSpa
      stkS caps 1
      phaseClosure 0

unsafe def captureNextBuf {s : String} (nfa : FlatNFA) (bufferSize : Nat) (p : Pos s) :
    Option (Buffer s bufferSize) :=
  let run := search nfa (Scratch.mkFor nfa.size.toNat bufferSize) (sentinelWord s) p
  if run.matched then
    some (toBuffer run.scratch.caps bufferSize)
  else
    none

/-- All non-overlapping matches, using the same empty-match advance as `Regex.Matches.next?`. -/
unsafe def findAll.go (nfa : FlatNFA) (info : OptimizationInfo) (haystack : String)
    (sent : UInt64) (pos : PosPlusOne haystack) (accum : Array Slice) (scratch : Scratch) : Array Slice :=
  if h : pos.isValid then
    let start := info.findStart (pos.asPos h)
    let run := search nfa scratch sent start
    if run.matched then
      let startPos := decode (uget run.scratch.caps 0)
      let stopPos := decode (uget run.scratch.caps slotBytes)
      if hv : stopPos.isValid = true ∧ startPos ≤ stopPos then
        have isStopPosValid : stopPos.isValid := hv.1
        have h' : startPos.isValid := PosPlusOne.isValid_of_isValid_of_le isStopPosValid hv.2
        have hle : (startPos.asPos h').offset ≤ (stopPos.asPos isStopPosValid).offset := by
          simpa [PosPlusOne.asPos_def] using (PosPlusOne.le_iff.mp hv.2)
        let slice : Slice :=
          ⟨haystack, startPos.asPos h', stopPos.asPos isStopPosValid, String.Pos.le_iff.mpr hle⟩
        let nextPos := PosPlusOne.pos (stopPos.asPos isStopPosValid)
        let next := if pos < nextPos then nextPos else pos.next h
        findAll.go nfa info haystack sent next (accum.push slice) run.scratch
      else
        accum
    else
      accum
  else
    accum

unsafe def findAll (nfa : FlatNFA) (info : OptimizationInfo) (haystack : String) : Array Slice :=
  -- One scratch block for every match. Capture rows are overwritten in place.
  findAll.go nfa info haystack (sentinelWord haystack) haystack.startPosPlusOne #[]
    (Scratch.mkFor nfa.size.toNat 2)

unsafe def count (nfa : FlatNFA) (info : OptimizationInfo) (haystack : String) : Nat :=
  (findAll nfa info haystack).size

unsafe def byteSpans (slices : Array Slice) : Array (Nat × Nat) :=
  slices.map fun s => (s.startInclusive.offset.byteIdx, s.endExclusive.offset.byteIdx)

/-- Byte offsets of a capture buffer. Proof fields are not compared. -/
def bufferOffsets {s : String} {n : Nat} (b : Buffer s n) : List Nat :=
  List.ofFn fun i : Fin n => (b[i]).offset.byteIdx

/--
Compare capture slots against the stock `BufferStrategy` at every position.
`none` means every slot offset agrees.
-/
unsafe def buffersAgree.go {haystack : String} (pattern : String) (re : Regex) (flat : FlatNFA)
    (bufSize : Nat) (pos : PosPlusOne haystack) : Option String :=
  if h : pos.isValid then
    let p := pos.asPos h
    let stock := re.captureNextBuf bufSize p
    let refined := captureNextBuf flat bufSize (re.optimizationInfo.findStart p)
    let same :=
      match stock, refined with
      | none, none => true
      | some a, some b => bufferOffsets a == bufferOffsets b
      | _, _ => false
    if same then
      buffersAgree.go pattern re flat bufSize (pos.next h)
    else
      some s!"buffer mismatch /{pattern}/ at {p.offset.byteIdx}"
  else
    none

unsafe def buffersAgree (pattern haystack : String) : Option String :=
  let re := Regex.parse! pattern
  match ofNFA re.nfa with
  | none => some s!"flat conversion failed for /{pattern}/"
  | some flat =>
    buffersAgree.go pattern re flat (re.maxTag + 1) haystack.startPosPlusOne

/-- Compare match spans against the stock VM. `none` means they agree. -/
unsafe def mismatch? (pattern haystack : String) : Option String :=
  let re := Regex.parse! pattern
  match ofNFA re.nfa with
  | none => some s!"flat conversion failed for /{pattern}/"
  | some flat =>
    let vm := byteSpans (re.findAll haystack)
    let fl := byteSpans (findAll flat re.optimizationInfo haystack)
    if vm == fl then
      none
    else
      some s!"mismatch /{pattern}/ on {haystack}: vm={vm} refined={fl}"

unsafe def selfCheck : Array String :=
  let cases : Array (String × String) := #[
    ("", ""),
    ("", "abc"),
    ("a", "a"),
    ("a", "b"),
    ("a*", ""),
    ("a*", "aaa"),
    ("a*", "baaac"),
    ("a+", "baaac"),
    ("a?", "a"),
    ("a?", ""),
    ("a|b", "ababa"),
    ("bool|boolean", "boolean"),
    ("a|ab", "ab"),
    ("(a+)(b*)", "aaabb"),
    ("(a+)(b*)|(c+)", "a aa aab c cc"),
    ("\\d{4}-\\d{2}-\\d{2}", "2025-05-24: x\n2025-05-26: y"),
    (".*", "abc\ndef"),
    ("^a", "a\na"),
    ("a$", "ba\na"),
    ("\\bword\\b", "a word wordy word"),
    ("[a-z]+", "AbCdefGHI"),
    ("[^A-Za-z]+", "aあb漢c"),
    ("[あ-ん]+", "アあいうア"),
    ("\\w", "あa_"),
    (".", "あ\nb"),
    ("[0-9]+", "id 42 and 7"),
    ("\\w+", "foo_bar baz"),
    ("a{2,4}", "aaaaaaaa"),
    ("(ab)+", "abababxab"),
    ("(a|aa)*", "aaaa"),
    ("(a*)*", "aaa"),
    ("a*", "bbbb"),
    (".", "é"),
    ("é+", "aéééb")
  ]
  cases.filterMap fun (pat, hay) => mismatch? pat hay <|> buffersAgree pat hay

end Regex.VM.Refined

end
