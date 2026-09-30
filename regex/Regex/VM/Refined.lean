module

public import Regex.Data.Anchor
public import Regex.Data.Classes
public import Regex.Data.String
public import Regex.NFA.Basic
public import Regex.Regex.Basic
public import Regex.Regex.OptimizationInfo
public import Regex.Regex.Utilities
public import Regex.Strategy

open Regex.Data (Anchor Classes)
open String (Pos PosPlusOne Slice)

/-!
Refined PikeVM.

The stock VM loads each NFA state as a boxed `NFA.Node` and pushes ε-work onto a `List`.
This module keeps the same Thompson NFA and the same left-biased PikeVM schedule, but stores
states in a flat scalar buffer and the ε-stack in reusable arrays so the hot loop does not
allocate a node, a cons cell, or a search-state wrapper.

`WordArray` is a one-field wrapper around an array of unboxed `UInt32`s. Lean erases that
wrapper (trivial-structure elimination), the same way it inlines the `ByteArray` and `FloatArray`
constructors and keeps only the scalar payload. Each state is three contiguous words
(tag, next, extra), loaded once from a single base index.
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

/--
Flat word buffer. The single field is erased, so a `WordArray` is the underlying array at runtime.
-/
structure WordArray where
  data : Array UInt32

/-- Three `UInt32`s per state: tag, next, extra. `abbrev` so the scale folds to an immediate. -/
abbrev stride : USize := 3

@[inline]
def push3 (a : Array UInt32) (tag next extra : UInt32) : Array UInt32 :=
  a.push tag |>.push next |>.push extra

/-- One unboxed word. `UInt32` is a tagged scalar, so the array load does not chase a node. -/
@[inline]
unsafe def wordGet (a : Array UInt32) (i : USize) : UInt32 :=
  a.uget i lcProof

/-- Flat NFA. `classes` holds the boxed character-class payloads referenced by `.sparse` states. -/
structure FlatNFA where
  words : WordArray
  classes : Array Classes
  size : UInt32
  start : UInt32

def anchorKind : Anchor → UInt32
  | .start => 0
  | .eos => 1
  | .wordBoundary => 2
  | .nonWordBoundary => 3

def encode (classes : Array Classes) : NFA.Node → Option (UInt32 × UInt32 × UInt32 × Array Classes)
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
      some (tagSparse, next.toUInt32, classes.size.toUInt32, classes.push cs)
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
    go 0 (Array.emptyWithCapacity (nfa.size * 3)) #[]
where
  go (i : Nat) (words : Array UInt32) (classes : Array Classes) : Option FlatNFA :=
    if h : i < nfa.nodes.size then
      match encode classes nfa.nodes[i] with
      | none => none
      | some (tag, next, extra, classes') =>
        go (i + 1) (push3 words tag next extra) classes'
    else
      some {
        words := ⟨words⟩
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
Reusable sparse-set and ε-stack buffers. Counts are not stored: each search starts them at zero,
which is the usual sparse-set clear.
-/
structure Scratch {s : String} (σ : Strategy s) where
  cDen : Array UInt32
  cSpa : Array UInt32
  nDen : Array UInt32
  nSpa : Array UInt32
  stkS : Array UInt32
  cUpd : Array σ.Update
  nUpd : Array σ.Update
  stkU : Array σ.Update

def Scratch.mkFor {s : String} (σ : Strategy s) (n : Nat) : Scratch σ :=
  let cap := max (n * 4) 8
  {
    cDen := Array.replicate n (0 : UInt32)
    cSpa := Array.replicate n (0 : UInt32)
    nDen := Array.replicate n (0 : UInt32)
    nSpa := Array.replicate n (0 : UInt32)
    stkS := Array.replicate cap (0 : UInt32)
    cUpd := Array.replicate n σ.empty
    nUpd := Array.replicate n σ.empty
    stkU := Array.replicate cap σ.empty
  }

structure SearchRun {s : String} (σ : Strategy s) where
  result : Option σ.Update
  scratch : Scratch σ

@[inline]
def SearchRun.pack {s : String} {σ : Strategy s} (result : Option σ.Update)
    (cDen cSpa nDen nSpa stkS : Array UInt32) (cUpd nUpd stkU : Array σ.Update) : SearchRun σ :=
  { result, scratch := { cDen, cSpa, nDen, nSpa, stkS, cUpd, nUpd, stkU } }

/--
Tail-recursive PikeVM. Every recursive call is in tail position so the buffers stay unique:
`uset` updates the sparse sets and the ε-stack in place. `c*` is the set being read, `n*` the
set being written. `clos` is the match found by the closure currently running; `matched` is the
match already accepted by the search.

`p` is the position of the active `eachStepChar` loop. `cp` is the position of the closure
(where saves and anchors run). They differ only while a character transition's closure is in
progress: the remaining states of this character must still be tested at `p` if that closure
does not reach `.done`.
-/
unsafe def eval {s : String} (σ : Strategy s)
    (words : Array UInt32) (classes : Array Classes) (start : UInt32)
    (p cp : Pos s) (matched clos : Option σ.Update)
    (cCount : UInt32) (cDen cSpa : Array UInt32) (cUpd : Array σ.Update)
    (nCount : UInt32) (nDen nSpa : Array UInt32) (nUpd : Array σ.Update)
    (stkU : Array σ.Update) (stkS : Array UInt32) (sp : Nat)
    (phase i : UInt32) : SearchRun σ :=
  if phase == phaseStep then
    if hp : p = s.endPos then
      SearchRun.pack matched cDen cSpa nDen nSpa stkS cUpd nUpd stkU
    else if i == 0 && cCount == 0 && matched.isSome then
      SearchRun.pack matched cDen cSpa nDen nSpa stkS cUpd nUpd stkU
    else if i == cCount then
      if matched.isNone then
        let stkU := stkU.uset 0 σ.empty lcProof
        let stkS := stkS.uset 0 start lcProof
        eval σ words classes start (p.next hp) (p.next hp) none none
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS 1
          phaseClosure 0
      else
        eval σ words classes start (p.next hp) (p.next hp) matched none
          nCount nDen nSpa nUpd
          (0 : UInt32) cDen cSpa cUpd
          stkU stkS 0
          phaseStep 0
    else
      let state := wordGet cDen i.toUSize
      let base := state.toUSize * stride
      let tag := wordGet words base
      if tag == tagDone then
        -- Lower-priority threads lose to the `.done` state already in this set.
        eval σ words classes start p p matched none
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS sp
          phaseStep cCount
      else if tag == tagChar then
        let extra := wordGet words (base + 2)
        if (p.get hp).val == extra then
          let nextW := wordGet words (base + 1)
          let update := cUpd.uget state.toUSize lcProof
          let stkU := stkU.uset 0 update lcProof
          let stkS := stkS.uset 0 nextW lcProof
          eval σ words classes start p (p.next hp) matched none
            cCount cDen cSpa cUpd
            nCount nDen nSpa nUpd
            stkU stkS 1
            phaseStepClosure i
        else
          eval σ words classes start p p matched none
            cCount cDen cSpa cUpd
            nCount nDen nSpa nUpd
            stkU stkS sp
            phaseStep (i + 1)
      else if tag == tagSparse then
        let extra := wordGet words (base + 2)
        let cs := classes.uget extra.toUSize lcProof
        if p.get hp ∈ cs then
          let nextW := wordGet words (base + 1)
          let update := cUpd.uget state.toUSize lcProof
          let stkU := stkU.uset 0 update lcProof
          let stkS := stkS.uset 0 nextW lcProof
          eval σ words classes start p (p.next hp) matched none
            cCount cDen cSpa cUpd
            nCount nDen nSpa nUpd
            stkU stkS 1
            phaseStepClosure i
        else
          eval σ words classes start p p matched none
            cCount cDen cSpa cUpd
            nCount nDen nSpa nUpd
            stkU stkS sp
            phaseStep (i + 1)
      else
        eval σ words classes start p p matched none
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS sp
          phaseStep (i + 1)
  else if sp == 0 then
    -- `phaseClosure` always installs the closure result and steps at `cp`. A step-closure does
    -- too when it reached `.done`; otherwise the rest of this character is tested at `p`.
    if phase == phaseClosure || clos.isSome then
      eval σ words classes start cp cp clos none
        nCount nDen nSpa nUpd
        (0 : UInt32) cDen cSpa cUpd
        stkU stkS 0
        phaseStep 0
    else
      eval σ words classes start p p matched none
        cCount cDen cSpa cUpd
        nCount nDen nSpa nUpd
        stkU stkS 0
        phaseStep (i + 1)
  else
    let sp' := sp - 1
    let update := stkU.uget sp'.toUSize lcProof
    let state := stkS.uget sp'.toUSize lcProof
    let si := wordGet nSpa state.toUSize
    let seen := if si < nCount then wordGet nDen si.toUSize == state else false
    if seen then
      eval σ words classes start p cp matched clos
        cCount cDen cSpa cUpd
        nCount nDen nSpa nUpd
        stkU stkS sp'
        phase i
    else
      let base := state.toUSize * stride
      let tag := wordGet words base
      let nextW := wordGet words (base + 1)
      let extra := wordGet words (base + 2)
      let clos := if tag == tagDone then clos <|> some update else clos
      let nDen := nDen.uset nCount.toUSize state lcProof
      let nSpa := nSpa.uset state.toUSize nCount lcProof
      let nCount := nCount + 1
      let nUpd := if writesUpdate tag then nUpd.uset state.toUSize update lcProof else nUpd
      -- Two free slots cover a `.split` (next₂ under next₁, so next₁ is popped first).
      let stkU := if sp' + 2 <= stkU.size then stkU else stkU.push σ.empty |>.push σ.empty
      let stkS := if sp' + 2 <= stkS.size then stkS else stkS.push (0 : UInt32) |>.push 0
      if tag == tagEpsilon then
        let stkU := stkU.uset sp'.toUSize update lcProof
        let stkS := stkS.uset sp'.toUSize nextW lcProof
        eval σ words classes start p cp matched clos
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS (sp' + 1)
          phase i
      else if tag == tagSplit then
        let stkU := stkU.uset sp'.toUSize update lcProof
        let stkS := stkS.uset sp'.toUSize extra lcProof
        let stkU := stkU.uset (sp' + 1).toUSize update lcProof
        let stkS := stkS.uset (sp' + 1).toUSize nextW lcProof
        eval σ words classes start p cp matched clos
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS (sp' + 2)
          phase i
      else if tag == tagSave then
        let update := σ.write update extra.toNat cp
        let stkU := stkU.uset sp'.toUSize update lcProof
        let stkS := stkS.uset sp'.toUSize nextW lcProof
        eval σ words classes start p cp matched clos
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS (sp' + 1)
          phase i
      else if tag == tagAnchor then
        if anchorTest extra cp then
          let stkU := stkU.uset sp'.toUSize update lcProof
          let stkS := stkS.uset sp'.toUSize nextW lcProof
          eval σ words classes start p cp matched clos
            cCount cDen cSpa cUpd
            nCount nDen nSpa nUpd
            stkU stkS (sp' + 1)
            phase i
        else
          eval σ words classes start p cp matched clos
            cCount cDen cSpa cUpd
            nCount nDen nSpa nUpd
            stkU stkS sp'
            phase i
      else
        eval σ words classes start p cp matched clos
          cCount cDen cSpa cUpd
          nCount nDen nSpa nUpd
          stkU stkS sp'
          phase i

unsafe def search {s : String} (σ : Strategy s) (nfa : FlatNFA) (scratch : Scratch σ) (p : Pos s) :
    SearchRun σ :=
  if nfa.size == 0 then
    { result := none, scratch }
  else
    let words := nfa.words.data
    let classes := nfa.classes
    let start := nfa.start
    let { cDen, cSpa, nDen, nSpa, stkS, cUpd, nUpd, stkU } := scratch
    let stkU := stkU.uset 0 σ.empty lcProof
    let stkS := stkS.uset 0 start lcProof
    eval σ words classes start p p none none
      (0 : UInt32) cDen cSpa cUpd
      (0 : UInt32) nDen nSpa nUpd
      stkU stkS 1
      phaseClosure 0

unsafe def captureNext {s : String} (σ : Strategy s) (nfa : FlatNFA) (p : Pos s) : Option σ.Update :=
  (search σ nfa (Scratch.mkFor σ nfa.size.toNat) p).result

unsafe def captureNextBuf {s : String} (nfa : FlatNFA) (bufferSize : Nat) (p : Pos s) :
    Option (Buffer s bufferSize) :=
  captureNext (BufferStrategy s bufferSize) nfa p

/-- All non-overlapping matches, using the same empty-match advance as `Regex.Matches.next?`. -/
unsafe def findAll (nfa : FlatNFA) (info : OptimizationInfo) (haystack : String) : Array Slice :=
  let rec go (pos : PosPlusOne haystack) (accum : Array Slice) : Array Slice :=
    if h : pos.isValid then
      let start := info.findStart (pos.asPos h)
      match captureNextBuf nfa 2 start with
      | none => accum
      | some slots =>
        let startPos := slots[0]
        let stopPos := slots[1]
        if hv : stopPos.isValid && startPos ≤ stopPos then
          have isStopPosValid : stopPos.isValid := by grind
          have h' : startPos.isValid := PosPlusOne.isValid_of_isValid_of_le isStopPosValid (by grind)
          let slice : Slice :=
            ⟨haystack, startPos.asPos h', stopPos.asPos isStopPosValid, String.Pos.le_iff.mpr (by grind)⟩
          let nextPos := PosPlusOne.pos (stopPos.asPos isStopPosValid)
          let next := if pos < nextPos then nextPos else pos.next h
          go next (accum.push slice)
        else
          accum
    else
      accum
  go haystack.startPosPlusOne #[]

unsafe def count (nfa : FlatNFA) (info : OptimizationInfo) (haystack : String) : Nat :=
  (findAll nfa info haystack).size

unsafe def byteSpans (slices : Array Slice) : Array (Nat × Nat) :=
  slices.map fun s => (s.startInclusive.offset.byteIdx, s.endExclusive.offset.byteIdx)

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
  cases.filterMap fun (pat, hay) => mismatch? pat hay

end Regex.VM.Refined

end
