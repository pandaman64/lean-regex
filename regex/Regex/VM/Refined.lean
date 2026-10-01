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

import Regex.Data.SparseSet.Bijection

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
      match ClassTable.compile cs with
      | some table =>
        some (tagSparse, next.toUInt32, classes.size.toUInt32, classes.push table)
      | none => none
    else
      none

/--
Translate `nfa` into the flat buffer.

Returns `none` when the NFA is empty, when `nfa.size * 12` does not fit in `2^32`
(a state byte offset would not round-trip through `USize` on a 32-bit platform),
when a save slot does not fit in `UInt32`, or when a character class's high runs
do not fit in a 32-bit offset.
-/
def ofNFA (nfa : NFA) : Option FlatNFA :=
  if nfa.size = 0 || nfa.size > 2 ^ 32 / 12 then
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

private theorem push3_data_size (words : WordArray) (a b c : UInt32) :
    (((words.push a).push b).push c).data.size = words.data.size + 12 := by
  rw [WordArray.data_size_push, WordArray.data_size_push, WordArray.data_size_push]

private theorem toNat_toUInt32_of_lt {n : Nat} (h : n < UInt32.size) : n.toUInt32.toNat = n := by
  rw [Nat.toUInt32_eq]
  simp [UInt32.ofNat, UInt32.toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by simpa [UInt32.size] using h)]

private theorem ofNFA.go_some {nfa : NFA} {flat : FlatNFA} (i : Nat) (words : WordArray)
    (classes : Array ClassTable) (hi : i ≤ nfa.nodes.size) (hlen : words.data.size = 12 * i)
    (h : ofNFA.go nfa i words classes = some flat) :
    flat.words.data.size = 12 * nfa.nodes.size ∧ flat.size = nfa.size.toUInt32 ∧
      flat.start = nfa.start.toUInt32 := by
  unfold ofNFA.go at h
  by_cases ilt : i < nfa.nodes.size
  · simp [ilt] at h
    match henc : encode classes nfa.nodes[i] with
    | none => simp [henc] at h
    | some (tag, next, extra, classes') =>
      simp [henc] at h
      have hlen' : (((words.push tag).push next).push extra).data.size = 12 * (i + 1) := by
        rw [push3_data_size, hlen]
        omega
      exact ofNFA.go_some (i + 1) _ classes' (Nat.succ_le_of_lt ilt) hlen' h
  · simp [ilt] at h
    cases h
    have ieq : i = nfa.nodes.size := Nat.le_antisymm hi (Nat.le_of_not_lt ilt)
    exact ⟨by rw [hlen, ieq], rfl, rfl⟩
termination_by nfa.nodes.size - i

/--
A successful flattening stores three words per state, and the state window fits in `2^32` bytes.
-/
theorem ofNFA_spec {nfa : NFA} {flat : FlatNFA} (h : ofNFA nfa = some flat) :
    0 < nfa.size ∧ nfa.size < UInt32.size ∧ nfa.size * 12 ≤ 2 ^ 32 ∧
      flat.size.toNat = nfa.size ∧ flat.start.toNat = nfa.start ∧
      flat.words.data.size = 12 * nfa.size ∧ flat.words.size = nfa.size * 3 := by
  unfold ofNFA at h
  split at h
  · simp at h
  · rename_i hok
    have hnot : decide (nfa.size = 0) = false ∧ decide (nfa.size > 2 ^ 32 / 12) = false := by
      simpa [Bool.or_eq_true] using hok
    have hpos : 0 < nfa.size := by
      have : ¬ nfa.size = 0 := by simpa using hnot.1
      omega
    have hwindow : nfa.size ≤ 2 ^ 32 / 12 := by
      have : ¬ nfa.size > 2 ^ 32 / 12 := by simpa using hnot.2
      omega
    have hbytes : nfa.size * 12 ≤ 2 ^ 32 := Nat.mul_le_of_le_div 12 nfa.size (2 ^ 32) hwindow
    have hfit : nfa.size < UInt32.size := by
      have : 2 ^ 32 / 12 < UInt32.size := by decide
      exact Nat.lt_of_le_of_lt hwindow this
    have hempty : (WordArray.emptyWithCapacity (nfa.size * 3)).data.size = 12 * 0 := by
      simp [WordArray.emptyWithCapacity_data_size]
    obtain ⟨hdata, hsize, hstart⟩ :=
      ofNFA.go_some 0 (WordArray.emptyWithCapacity (nfa.size * 3)) #[] (Nat.zero_le _) hempty h
    refine ⟨hpos, hfit, hbytes, ?_, ?_, ?_, ?_⟩
    · rw [hsize, toNat_toUInt32_of_lt hfit]
    · have hstartLt : nfa.start < UInt32.size := by
        have hs : nfa.start = nfa.size - 1 := rfl
        have hlt : nfa.start < nfa.size := by omega
        exact Nat.lt_trans hlt hfit
      rw [hstart, toNat_toUInt32_of_lt hstartLt]
    · rw [hdata, show nfa.size = nfa.nodes.size from rfl]
    · rw [WordArray.size_eq_data_div, hdata, show nfa.size = nfa.nodes.size from rfl]
      omega

/-- State `state` occupies bytes `[12 * state, 12 * state + 12)`. -/
theorem ofNFA_stateBytes {nfa : NFA} {flat : FlatNFA} (h : ofNFA nfa = some flat)
    (state : Nat) (hs : state < nfa.size) : state * 12 + 12 ≤ flat.words.data.size := by
  have spec := ofNFA_spec h
  omega

/-- The byte offset of `state` is below `2^32`, so it round-trips through `USize`. -/
theorem ofNFA_stateOff_lt {nfa : NFA} {flat : FlatNFA} (h : ofNFA nfa = some flat)
    (state : Nat) (hs : state < nfa.size) : state * 12 < 2 ^ 32 := by
  have spec := ofNFA_spec h
  omega

/--
Read the word whose first byte is `off`.

Out-of-range offsets are `0`. The in-range case does not mention the bound proofs,
so a later rewrite of `off` stays type-correct.
-/
def wordAt (w : WordArray) (off : Nat) : UInt32 :=
  if h : off + 4 ≤ w.data.size ∧ off < 2 ^ 32 then
    w.uget off.toUSize (by
      rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h.2]
      exact h.1)
  else
    0

/--
Three words decode to `node`. A `.sparse` node stores the index of the table
`ClassTable.compile` produced for its class.
-/
def Encodes (classes : Array ClassTable) (node : NFA.Node) (tag next extra : UInt32) : Prop :=
  match node with
  | .done => tag = tagDone ∧ next = 0 ∧ extra = 0
  | .fail => tag = tagFail ∧ next = 0 ∧ extra = 0
  | .epsilon nxt => tag = tagEpsilon ∧ next = nxt.toUInt32 ∧ extra = 0
  | .anchor a nxt => tag = tagAnchor ∧ next = nxt.toUInt32 ∧ extra = anchorKind a
  | .char c nxt => tag = tagChar ∧ next = nxt.toUInt32 ∧ extra = c.val
  | .split n₁ n₂ => tag = tagSplit ∧ next = n₁.toUInt32 ∧ extra = n₂.toUInt32
  | .save off nxt =>
      off < UInt32.size ∧ tag = tagSave ∧ next = nxt.toUInt32 ∧ extra = off.toUInt32
  | .sparse cs nxt =>
      tag = tagSparse ∧ next = nxt.toUInt32 ∧
        ∃ t : ClassTable, ClassTable.compile cs = some t ∧ classes[extra.toNat]? = some t

private theorem encodes_push {classes : Array ClassTable} {node : NFA.Node} {tag next extra : UInt32}
    {pushed : ClassTable} (h : Encodes classes node tag next extra) :
    Encodes (classes.push pushed) node tag next extra := by
  cases node with
  | sparse cs nxt =>
    simp only [Encodes] at h ⊢
    rcases h with ⟨htag, hnext, table, hcomp, hget⟩
    refine ⟨htag, hnext, table, hcomp, ?_⟩
    rcases Array.getElem?_eq_some_iff.mp hget with ⟨hlt, hval⟩
    rw [Array.getElem?_push_lt hlt]
    exact congrArg some hval
  | _ =>
    simp only [Encodes] at h ⊢
    exact h

private theorem some_words_inj {a b c : UInt32} {xs : Array ClassTable}
    {tag next extra : UInt32} {ys : Array ClassTable}
    (h : some (a, b, c, xs) = some (tag, next, extra, ys)) :
    tag = a ∧ next = b ∧ extra = c ∧ ys = xs := by
  injection h with h
  injection h with ha h
  injection h with hb h
  injection h with hc hys
  exact ⟨ha.symm, hb.symm, hc.symm, hys.symm⟩

/-- `encode` either keeps the class array or pushes the one table it just compiled. -/
private theorem encode_classes (classes : Array ClassTable) (node : NFA.Node)
    {tag next extra : UInt32} {classes' : Array ClassTable}
    (h : encode classes node = some (tag, next, extra, classes')) :
    classes' = classes ∨ ∃ t : ClassTable, classes' = classes.push t := by
  unfold encode at h
  split at h
  · exact Or.inl (some_words_inj h).2.2.2
  · exact Or.inl (some_words_inj h).2.2.2
  · exact Or.inl (some_words_inj h).2.2.2
  · exact Or.inl (some_words_inj h).2.2.2
  · exact Or.inl (some_words_inj h).2.2.2
  · exact Or.inl (some_words_inj h).2.2.2
  · split at h
    · exact Or.inl (some_words_inj h).2.2.2
    · simp at h
  · split at h
    · split at h
      · next table _ =>
        exact Or.inr ⟨table, (some_words_inj h).2.2.2⟩
      · simp at h
    · simp at h

private theorem encode_encodes (classes : Array ClassTable) (node : NFA.Node)
    {tag next extra : UInt32} {classes' : Array ClassTable}
    (h : encode classes node = some (tag, next, extra, classes')) :
    Encodes classes' node tag next extra := by
  unfold encode at h
  split at h
  · rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
    simp [Encodes]
  · rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
    simp [Encodes]
  · rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
    simp [Encodes]
  · rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
    simp [Encodes]
  · rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
    simp [Encodes]
  · rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
    simp [Encodes]
  · split at h
    · rename_i off nxt hoff
      rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
      exact ⟨hoff, rfl, rfl, rfl⟩
    · simp at h
  · split at h
    · split at h
      · rename_i _node cs nxt hsz _compiled table hc
        rcases some_words_inj h with ⟨rfl, rfl, rfl, rfl⟩
        refine ⟨rfl, rfl, table, hc, ?_⟩
        rw [toNat_toUInt32_of_lt hsz]
        exact Array.getElem?_push_size
      · simp at h
    · simp at h

private theorem wordAt_push (w : WordArray) (v : UInt32) (off : Nat)
    (hsize : off + 4 ≤ w.data.size) (hoff : off < 2 ^ 32) :
    wordAt (w.push v) off = wordAt w off := by
  have hpush : off + 4 ≤ (w.push v).data.size ∧ off < 2 ^ 32 := by
    rw [WordArray.data_size_push]
    exact ⟨by omega, hoff⟩
  have hhere : off + 4 ≤ w.data.size ∧ off < 2 ^ 32 := ⟨hsize, hoff⟩
  unfold wordAt
  rw [dite_eq_left hpush, dite_eq_left hhere]
  have hnat : off.toUSize.toNat + 4 ≤ w.data.size := by
    rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hoff]
    exact hsize
  have raw := WordArray.uget_push_lt w v off.toUSize hnat
  exact (congrArg (fun p => (w.push v).uget off.toUSize p) (proof_irrel _ _)).trans
    (raw.trans (congrArg (fun p => w.uget off.toUSize p) (proof_irrel _ _)).symm)

private theorem wordAt_push_new (w : WordArray) (v : UInt32) (hbase : w.data.size < 2 ^ 32) :
    wordAt (w.push v) w.data.size = v := by
  have hcond : w.data.size + 4 ≤ (w.push v).data.size ∧ w.data.size < 2 ^ 32 := by
    rw [WordArray.data_size_push]
    exact ⟨Nat.le_refl _, hbase⟩
  unfold wordAt
  rw [dite_eq_left hcond]
  have harg : w.data.size.toUSize.toNat + 4 ≤ (w.push v).data.size := by
    rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hbase, WordArray.data_size_push]
    exact Nat.le_refl _
  exact (congrArg (fun p => (w.push v).uget w.data.size.toUSize p) (proof_irrel _ harg)).trans
    (WordArray.uget_push w v harg hbase)

private theorem ofNFA.go_encodes {nfa : NFA} {flat : FlatNFA} (i : Nat) (words : WordArray)
    (classes : Array ClassTable) (hi : i ≤ nfa.nodes.size) (hlen : words.data.size = 12 * i)
    (hfit : 12 * nfa.nodes.size ≤ 2 ^ 32)
    (hpref : ∀ j, (hj : j < i) →
      Encodes classes nfa.nodes[j]
        (wordAt words (12 * j))
        (wordAt words (12 * j + 4))
        (wordAt words (12 * j + 8)))
    (h : ofNFA.go nfa i words classes = some flat) (j : Nat) (hj : j < nfa.nodes.size) :
    Encodes flat.classes nfa.nodes[j]
      (wordAt flat.words (12 * j))
      (wordAt flat.words (12 * j + 4))
      (wordAt flat.words (12 * j + 8)) := by
  unfold ofNFA.go at h
  by_cases ilt : i < nfa.nodes.size
  · simp [ilt] at h
    match henc : encode classes nfa.nodes[i] with
    | none => simp [henc] at h
    | some (tag, next, extra, classes') =>
      simp [henc] at h
      have hlen' : (((words.push tag).push next).push extra).data.size = 12 * (i + 1) := by
        rw [push3_data_size, hlen]
        omega
      have hnew : Encodes classes' nfa.nodes[i] tag next extra :=
        encode_encodes classes nfa.nodes[i] henc
      have hpref' : ∀ k, (hk : k < i + 1) →
          Encodes classes' nfa.nodes[k]
            (wordAt (((words.push tag).push next).push extra) (12 * k))
            (wordAt (((words.push tag).push next).push extra) (12 * k + 4))
            (wordAt (((words.push tag).push next).push extra) (12 * k + 8)) := by
        intro k hk
        by_cases hk' : k < i
        · have hmono : Encodes classes' nfa.nodes[k]
              (wordAt words (12 * k))
              (wordAt words (12 * k + 4))
              (wordAt words (12 * k + 8)) := by
            rcases encode_classes classes nfa.nodes[i] henc with rfl | ⟨_, rfl⟩
            · exact hpref k hk'
            · exact encodes_push (hpref k hk')
          have stable (off : Nat) (hsz : off + 4 ≤ words.data.size) (h32 : off < 2 ^ 32) :
              wordAt (((words.push tag).push next).push extra) off = wordAt words off :=
            (wordAt_push ((words.push tag).push next) extra off
                (by rw [WordArray.data_size_push, WordArray.data_size_push]; omega) h32).trans
              ((wordAt_push (words.push tag) next off
                  (by rw [WordArray.data_size_push]; omega) h32).trans
                (wordAt_push words tag off hsz h32))
          simpa [stable (12 * k) (by rw [hlen]; omega) (by omega),
            stable (12 * k + 4) (by rw [hlen]; omega) (by omega),
            stable (12 * k + 8) (by rw [hlen]; omega) (by omega)] using hmono
        · have keq : k = i := by omega
          subst k
          have hbase : words.data.size < 2 ^ 32 := by rw [hlen]; omega
          have hbase4 : words.data.size + 4 < 2 ^ 32 := by rw [hlen]; omega
          have ht : wordAt (((words.push tag).push next).push extra) (12 * i) = tag := by
            rw [show 12 * i = words.data.size by rw [hlen]]
            exact (wordAt_push ((words.push tag).push next) extra words.data.size
                (by
                  rw [WordArray.data_size_push (words.push tag) next,
                    WordArray.data_size_push words tag]
                  exact Nat.le_add_right _ _) hbase).trans
              ((wordAt_push (words.push tag) next words.data.size
                  (by
                    rw [WordArray.data_size_push words tag]
                    exact Nat.le_refl _) hbase).trans
                (wordAt_push_new words tag hbase))
          have hn : wordAt (((words.push tag).push next).push extra) (12 * i + 4) = next := by
            rw [show 12 * i + 4 = words.data.size + 4 by rw [hlen]]
            have h4 : (words.push tag).data.size = words.data.size + 4 := WordArray.data_size_push _ _
            rw [← h4]
            exact (wordAt_push ((words.push tag).push next) extra (words.push tag).data.size
                (by
                  rw [WordArray.data_size_push (words.push tag) next]
                  exact Nat.le_refl _)
                (by rw [h4]; exact hbase4)).trans
              (wordAt_push_new (words.push tag) next (by rw [h4]; exact hbase4))
          have he : wordAt (((words.push tag).push next).push extra) (12 * i + 8) = extra := by
            rw [show 12 * i + 8 = words.data.size + 8 by rw [hlen]]
            have h8 : ((words.push tag).push next).data.size = words.data.size + 8 := by
              rw [WordArray.data_size_push, WordArray.data_size_push]
            rw [← h8]
            exact wordAt_push_new ((words.push tag).push next) extra (by
              rw [h8, hlen]
              have hineq : i + 1 ≤ nfa.nodes.size := Nat.succ_le_of_lt ilt
              have hmul : 12 * (i + 1) ≤ 12 * nfa.nodes.size := Nat.mul_le_mul_left 12 hineq
              exact Nat.lt_of_lt_of_le (by omega : 12 * i + 8 < 12 * (i + 1)) (Nat.le_trans hmul hfit))
          simpa [ht, hn, he] using hnew
      exact ofNFA.go_encodes (i + 1) (((words.push tag).push next).push extra) classes'
        (Nat.succ_le_of_lt ilt) hlen' hfit hpref' h j hj
  · simp [ilt] at h
    cases h
    have ieq : i = nfa.nodes.size := Nat.le_antisymm hi (Nat.le_of_not_lt ilt)
    have hj' : j < i := by rw [ieq]; exact hj
    simpa [ieq] using hpref j hj'
termination_by nfa.nodes.size - i

/-- State `j` of a successful flattening is the three words of `nfa[j]`. -/
theorem ofNFA_encodes {nfa : NFA} {flat : FlatNFA} (h : ofNFA nfa = some flat)
    (j : Nat) (hj : j < nfa.size) :
    Encodes flat.classes nfa[j]
      (wordAt flat.words (12 * j))
      (wordAt flat.words (12 * j + 4))
      (wordAt flat.words (12 * j + 8)) := by
  have spec := ofNFA_spec h
  unfold ofNFA at h
  split at h
  · simp at h
  · have hempty : (WordArray.emptyWithCapacity (nfa.size * 3)).data.size = 12 * 0 := by
      simp [WordArray.emptyWithCapacity_data_size]
    have hfit : 12 * nfa.nodes.size ≤ 2 ^ 32 := by
      rw [show nfa.nodes.size = nfa.size from rfl]
      omega
    have hpref : ∀ k, (hk : k < 0) →
        Encodes #[] nfa.nodes[k]
          (wordAt (WordArray.emptyWithCapacity (nfa.size * 3)) (12 * k))
          (wordAt (WordArray.emptyWithCapacity (nfa.size * 3)) (12 * k + 4))
          (wordAt (WordArray.emptyWithCapacity (nfa.size * 3)) (12 * k + 8)) := by
      intro k hk
      omega
    exact ofNFA.go_encodes 0 (WordArray.emptyWithCapacity (nfa.size * 3)) #[] (Nat.zero_le _) hempty
      hfit hpref h j hj

/--
A transition target stored by `Encodes` is still below `nfa.size`.

`.done` and `.fail` store next word `0`, and `inBounds` does not force the NFA
to be nonempty, so the caller passes `0 < size` (from `WellFormed.size_lt`).
-/
theorem Encodes.next_lt {classes : Array ClassTable} {node : NFA.Node} {tag next extra : UInt32}
    {size : Nat} (h0 : 0 < size) (h : Encodes classes node tag next extra)
    (hb : node.inBounds size) (hs : size < 2 ^ 32) : next.toNat < size := by
  cases node with
  | done =>
    simp [Encodes] at h
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, UInt32.toNat_zero]
    exact h0
  | fail =>
    simp [Encodes] at h
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, UInt32.toNat_zero]
    exact h0
  | epsilon nxt =>
    simp [Encodes, NFA.Node.inBounds] at h hb
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, toNat_toUInt32_of_lt (Nat.lt_trans hb hs)]
    exact hb
  | anchor _ nxt =>
    simp [Encodes, NFA.Node.inBounds] at h hb
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, toNat_toUInt32_of_lt (Nat.lt_trans hb hs)]
    exact hb
  | char _ nxt =>
    simp [Encodes, NFA.Node.inBounds] at h hb
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, toNat_toUInt32_of_lt (Nat.lt_trans hb hs)]
    exact hb
  | split n₁ n₂ =>
    simp [Encodes, NFA.Node.inBounds] at h hb
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, toNat_toUInt32_of_lt (Nat.lt_trans hb.1 hs)]
    exact hb.1
  | save _ nxt =>
    simp [Encodes, NFA.Node.inBounds] at h hb
    rcases h with ⟨_, _, hnext, _⟩
    rw [hnext, toNat_toUInt32_of_lt (Nat.lt_trans hb hs)]
    exact hb
  | sparse _ nxt =>
    simp [Encodes, NFA.Node.inBounds] at h hb
    rcases h with ⟨_, hnext, _⟩
    rw [hnext, toNat_toUInt32_of_lt (Nat.lt_trans hb hs)]
    exact hb

/-- The second target of a `.split` is below `nfa.size`. -/
theorem Encodes.split_extra_lt {classes : Array ClassTable} {n₁ n₂ : Nat} {tag next extra : UInt32}
    {size : Nat} (h : Encodes classes (.split n₁ n₂) tag next extra)
    (hb : n₂ < size) (hs : size < 2 ^ 32) : extra.toNat < size := by
  simp [Encodes] at h
  rcases h with ⟨_, _, hextra⟩
  rw [hextra, toNat_toUInt32_of_lt (Nat.lt_trans hb hs)]
  exact hb

/-- A `.sparse` word indexes the class table that was compiled for that node. -/
theorem Encodes.sparse_idx {classes : Array ClassTable} {cs : Regex.Data.Classes} {nxt : Nat}
    {tag next extra : UInt32} (h : Encodes classes (.sparse cs nxt) tag next extra) :
    extra.toNat < classes.size := by
  simp [Encodes] at h
  rcases h with ⟨_, _, _, _, hget⟩
  rcases Array.getElem?_eq_some_iff.mp hget with ⟨hlt, _⟩
  exact hlt

@[inline]
def anchorOf (k : UInt32) : Anchor :=
  if k == 0 then .start
  else if k == 1 then .eos
  else if k == 2 then .wordBoundary
  else .nonWordBoundary

/--
Previous character, using the C UTF-8 walker (`lean_string_utf8_prev`).

`String.Pos.prev` builds a `Slice` and scans backward in Lean. The walker steps
at most four bytes to the previous scalar, which is what a Unicode word
property needs. Classification stays `Char.isWordChar`.
-/
@[inline]
def prevWord {s : String} (p : Pos s) : Bool :=
  if p == s.startPos then
    false
  else
    Char.isWordChar (String.Pos.Raw.get s (String.Pos.Raw.prev s p.offset))

/-- Start, end, or a word-boundary test. Word characters still go through `Char.isWordChar`. -/
@[inline]
def anchorTest {s : String} (k : UInt32) (p : Pos s) : Bool :=
  if k == 0 then
    p == s.startPos
  else if k == 1 then
    p == s.endPos
  else
    let curr := Regex.Data.String.isCurrWord p
    let prev := prevWord p
    if k == 2 then curr != prev else curr == prev

private theorem indexBytes (i : Nat) (hi : i < 2 ^ 30) :
    (i.toUSize * Regex.VM.Wide.wordBytes).toNat = 4 * i := by
  have hi32 : i < 2 ^ 32 := by omega
  have h4 : Regex.VM.Wide.wordBytes.toNat = 4 := by
    simp [Regex.VM.Wide.wordBytes, Regex.VM.Wide.toNat_uSize_ofNat_of_lt 4 (by decide)]
  rw [USize.toNat_mul, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hi32, h4, Nat.mul_comm i 4]
  exact Nat.mod_eq_of_lt
    (Regex.VM.Wide.lt_two_pow_numBits_of_lt_2_pow_32 (by omega : 4 * i < 2 ^ 32))

private theorem wordIndex (i : Nat) (hi : i < 2 ^ 30) :
    i.toUSize * Regex.VM.Wide.wordBytes = (4 * i).toUSize := by
  apply USize.toNat_inj.mp
  rw [indexBytes i hi, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (by omega)]

private theorem wordAt_eq (a : WordArray) (off : Nat)
    (hsize : off + 4 ≤ a.data.size) (h32 : off < 2 ^ 32) :
    wordAt a off = a.uget off.toUSize (by
      rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]
      exact hsize) := by
  unfold wordAt
  have hcond : off + 4 ≤ a.data.size ∧ off < 2 ^ 32 := ⟨hsize, h32⟩
  simp [hcond, ↓reduceDIte]

private theorem wordAt_usetWord (a : WordArray) (i : Nat) (v : UInt32)
    (h : (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size) (hi : i < 2 ^ 30) :
    wordAt (a.usetWord i.toUSize v h) (4 * i) = v := by
  have hsize := (WordArray.size_uset a (i.toUSize * Regex.VM.Wide.wordBytes) v h).1
  have h32 : 4 * i < 2 ^ 32 := by omega
  have hnat : 4 * i + 4 ≤ a.data.size := by
    rw [indexBytes i hi] at h
    exact h
  have hcond : 4 * i + 4 ≤ (a.usetWord i.toUSize v h).data.size ∧ 4 * i < 2 ^ 32 := by
    rw [WordArray.usetWord_eq, hsize]
    exact ⟨hnat, h32⟩
  unfold wordAt
  rw [dite_eq_left hcond]
  have hbound : (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤
      (a.usetWord i.toUSize v h).data.size := by
    rw [WordArray.usetWord_eq, hsize]
    exact h
  exact (WordArray.uget_off_eq (a.usetWord i.toUSize v h) ((4 * i).toUSize)
      (i.toUSize * Regex.VM.Wide.wordBytes) _ hbound (wordIndex i hi).symm).trans
    (WordArray.uget_uset a (i.toUSize * Regex.VM.Wide.wordBytes) v h hbound)

private theorem wordAt_usetWord_ne (a : WordArray) (i j : Nat) (v : UInt32)
    (h : (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size)
    (hi : i < 2 ^ 30) (hj : j < 2 ^ 30) (hne : i ≠ j)
    (hjSize : 4 * j + 4 ≤ a.data.size) :
    wordAt (a.usetWord i.toUSize v h) (4 * j) = wordAt a (4 * j) := by
  have hsize := (WordArray.size_uset a (i.toUSize * Regex.VM.Wide.wordBytes) v h).1
  have h32 : 4 * j < 2 ^ 32 := by omega
  have hcond : 4 * j + 4 ≤ (a.usetWord i.toUSize v h).data.size ∧ 4 * j < 2 ^ 32 := by
    rw [WordArray.usetWord_eq, hsize]
    exact ⟨hjSize, h32⟩
  have hhere : 4 * j + 4 ≤ a.data.size ∧ 4 * j < 2 ^ 32 := ⟨hjSize, h32⟩
  unfold wordAt
  rw [dite_eq_left hcond, dite_eq_left hhere]
  have hread : ((4 * j).toUSize).toNat + 4 ≤ a.data.size := by
    rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]
    exact hjSize
  have h' : ((4 * j).toUSize).toNat + 4 ≤ (a.usetWord i.toUSize v h).data.size := by
    rw [WordArray.usetWord_eq, hsize]
    exact hread
  have hdisj : ((4 * j).toUSize).toNat + 4 ≤ (i.toUSize * Regex.VM.Wide.wordBytes).toNat ∨
      (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ ((4 * j).toUSize).toNat := by
    rw [indexBytes i hi, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]
    rcases Nat.lt_trichotomy i j with hlt | heq | hgt
    · right
      omega
    · exact absurd heq hne
    · left
      omega
  exact (congrArg
      (fun p => (a.usetWord i.toUSize v h).uget ((4 * j).toUSize) p) (proof_irrel _ h')).trans
    ((WordArray.uget_uset_disjoint a (i.toUSize * Regex.VM.Wide.wordBytes) ((4 * j).toUSize) v h
      hread hdisj h').trans
      (congrArg (fun p => a.uget ((4 * j).toUSize) p) (proof_irrel hread _)).symm)

/-- Indices and values that agree propositionally write the same word. -/
private theorem usetWord_rfl {a : WordArray} {i j : USize} {v w : UInt32}
    {hi : (i * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size}
    {hj : (j * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size}
    (hij : i = j) (hvw : v = w) : a.usetWord i v hi = a.usetWord j w hj := by
  subst hij
  subst hvw
  rfl

/-- A word load does not depend on which in-bounds proof it is given. -/
private theorem ugetWord_irrel (a : WordArray) (i : USize)
    (h₁ h₂ : (i * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size) :
    a.ugetWord i h₁ = a.ugetWord i h₂ := rfl

/--
Live prefix of the ε-stack.

`sp ≤ stkS.size` is the stack bound. Each live slot is a state id below `nStates`,
so it is a `Fin nStates`. `sp ≤ 2^30` keeps every live byte offset strictly below
`2^32`, which is what makes the `USize` index round-trip on a 32-bit platform.
-/
structure StackInv (stkS : WordArray) (sp nStates : Nat) : Prop where
  sp_le : sp ≤ stkS.size
  sp_fit : sp ≤ 2 ^ 30
  div4 : 4 * stkS.size = stkS.data.size
  id_lt : ∀ i, i < sp → (wordAt stkS (4 * i)).toNat < nStates

namespace StackInv

variable {stkS : WordArray} {sp nStates : Nat}

/-- The state id in live slot `i`. -/
def state (h : StackInv stkS sp nStates) (i : Nat) (hi : i < sp) : Fin nStates :=
  ⟨(wordAt stkS (4 * i)).toNat, h.id_lt i hi⟩

theorem wordBound (h : StackInv stkS sp nStates) (i : Nat)
    (hi : i < stkS.size) (hfit : i < 2 ^ 30) :
    (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ stkS.data.size := by
  rw [indexBytes i hfit]
  have hmul : 4 * (i + 1) ≤ 4 * stkS.size := Nat.mul_le_mul_left 4 (Nat.succ_le_of_lt hi)
  rw [h.div4] at hmul
  omega

theorem readWord (h : StackInv stkS sp nStates) (i : Nat) (hi : i < sp) :
    stkS.ugetWord i.toUSize
        (h.wordBound i (Nat.lt_of_lt_of_le hi h.sp_le) (Nat.lt_of_lt_of_le hi h.sp_fit)) =
      wordAt stkS (4 * i) := by
  have hfit := Nat.lt_of_lt_of_le hi h.sp_fit
  have hw := h.wordBound i (Nat.lt_of_lt_of_le hi h.sp_le) hfit
  rw [WordArray.ugetWord]
  have h32 : 4 * i < 2 ^ 32 := by omega
  have hnat : 4 * i + 4 ≤ stkS.data.size := by
    have hb := hw
    rw [indexBytes i hfit] at hb
    exact hb
  rw [wordAt_eq stkS (4 * i) hnat h32]
  exact WordArray.uget_off_eq stkS _ _ hw
    (by
      rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]
      exact hnat)
    (wordIndex i hfit)

theorem pop (h : StackInv stkS sp nStates) (hsp : 0 < sp) :
    StackInv stkS (sp - 1) nStates :=
  have hlt : sp - 1 < sp := Nat.sub_lt hsp (by decide)
  ⟨Nat.le_trans (Nat.le_of_lt hlt) h.sp_le, Nat.le_trans (Nat.le_of_lt hlt) h.sp_fit, h.div4,
    fun i hi => h.id_lt i (Nat.lt_trans hi hlt)⟩

theorem write (h : StackInv stkS sp nStates) (i : Nat) (hi : i < sp)
    (v : UInt32) (hv : v.toNat < nStates) :
    StackInv (stkS.usetWord i.toUSize v
      (h.wordBound i (Nat.lt_of_lt_of_le hi h.sp_le) (Nat.lt_of_lt_of_le hi h.sp_fit))) sp nStates := by
  have hw := h.wordBound i (Nat.lt_of_lt_of_le hi h.sp_le) (Nat.lt_of_lt_of_le hi h.sp_fit)
  have hsz := WordArray.size_uset stkS (i.toUSize * Regex.VM.Wide.wordBytes) v hw
  refine ⟨?_, h.sp_fit, ?_, ?_⟩
  · rw [WordArray.usetWord_eq, hsz.2]; exact h.sp_le
  · rw [WordArray.usetWord_eq, hsz.1, hsz.2]; exact h.div4
  · intro j hj
    by_cases hje : j = i
    · subst j
      rw [wordAt_usetWord _ _ _ hw (Nat.lt_of_lt_of_le hi h.sp_fit)]
      exact hv
    · have hj30 : j < 2 ^ 30 := Nat.lt_of_lt_of_le hj h.sp_fit
      have hjSize : 4 * j + 4 ≤ stkS.data.size := by
        have hb := h.wordBound j (Nat.lt_of_lt_of_le hj h.sp_le) hj30
        rw [indexBytes j hj30] at hb
        exact hb
      rw [wordAt_usetWord_ne _ _ _ _ hw (Nat.lt_of_lt_of_le hi h.sp_fit) hj30 (Ne.symm hje) hjSize]
      exact h.id_lt j hj

theorem push (h : StackInv stkS sp nStates) (hroom : sp < stkS.size) (hfit : sp < 2 ^ 30)
    (v : UInt32) (hv : v.toNat < nStates) :
    StackInv (stkS.usetWord sp.toUSize v (h.wordBound sp hroom hfit)) (sp + 1) nStates := by
  have hw := h.wordBound sp hroom hfit
  have hsz := WordArray.size_uset stkS (sp.toUSize * Regex.VM.Wide.wordBytes) v hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [WordArray.usetWord_eq, hsz.2]; omega
  · omega
  · rw [WordArray.usetWord_eq, hsz.1, hsz.2]; exact h.div4
  · intro j hj
    by_cases hje : j = sp
    · subst j
      rw [wordAt_usetWord _ _ _ hw hfit]
      exact hv
    · have hj' : j < sp := by omega
      have hj30 : j < 2 ^ 30 := Nat.lt_of_lt_of_le hj' h.sp_fit
      have hjSize : 4 * j + 4 ≤ stkS.data.size := by
        have hb := h.wordBound j (Nat.lt_of_lt_of_le hj' h.sp_le) hj30
        rw [indexBytes j hj30] at hb
        exact hb
      rw [wordAt_usetWord_ne _ _ _ _ hw hfit hj30 (Ne.symm hje) hjSize]
      exact h.id_lt j hj'

/-- Pushing two zero words does not change the live prefix. -/
theorem grow2 (h : StackInv stkS sp nStates) :
    StackInv ((stkS.push 0).push 0) sp nStates := by
  have h1 := WordArray.push_div4 stkS 0 h.div4
  have h2 := WordArray.push_div4 (stkS.push 0) 0 h1.2
  refine ⟨?_, h.sp_fit, h2.2, ?_⟩
  · rw [h2.1, h1.1]
    exact Nat.le_trans h.sp_le (Nat.le_add_right stkS.size (1 + 1))
  · intro i hi
    have h30 : i < 2 ^ 30 := Nat.lt_of_lt_of_le hi h.sp_fit
    have hle : 4 * i + 4 ≤ stkS.data.size := by
      have hb := h.wordBound i (Nat.lt_of_lt_of_le hi h.sp_le) h30
      rw [indexBytes i h30] at hb
      exact hb
    have h32 : 4 * i < 2 ^ 32 := by omega
    have hmid : 4 * i + 4 ≤ (stkS.push 0).data.size := by
      rw [WordArray.data_size_push]
      omega
    rw [wordAt_push (stkS.push 0) 0 (4 * i) hmid h32, wordAt_push stkS 0 (4 * i) hle h32]
    exact h.id_lt i hi

/-- Pop, then push one successor into the same slot. Depth is unchanged. -/
theorem stepSucc (h : StackInv stkS sp nStates) (hsp : 0 < sp)
    (v : UInt32) (hv : v.toNat < nStates) :
    StackInv (stkS.usetWord (sp - 1).toUSize v
      (h.wordBound (sp - 1)
        (Nat.lt_of_lt_of_le (Nat.sub_lt hsp (by decide)) h.sp_le)
        (Nat.lt_of_lt_of_le (Nat.sub_lt hsp (by decide)) h.sp_fit))) sp nStates :=
  h.write (sp - 1) (Nat.sub_lt hsp (by decide)) v hv

/--
Write the two successors of a `.split`. `v0` replaces the popped slot and `v1` is
pushed above it, so the new depth is `sp + 1`. `sp < stkS.size` is the room for
that push: the closure grows by two words first when the live prefix fills the buffer.
`sp + 1 ≤ 2^30` keeps the new top inside a 32-bit byte offset.
-/
theorem stepSplit (h : StackInv stkS sp nStates) (hsp : 0 < sp)
    (hroom : sp < stkS.size) (hfit : sp + 1 ≤ 2 ^ 30)
    (v0 v1 : UInt32) (hv0 : v0.toNat < nStates) (hv1 : v1.toNat < nStates) :
    let hi : sp - 1 < sp := Nat.sub_lt hsp (by decide)
    let hw := h.write (sp - 1) hi v0 hv0
    StackInv
      ((stkS.usetWord (sp - 1).toUSize v0
          (h.wordBound (sp - 1) (Nat.lt_of_lt_of_le hi h.sp_le)
            (Nat.lt_of_lt_of_le hi h.sp_fit))).usetWord
        sp.toUSize v1
        (hw.wordBound sp
          (by
            rw [WordArray.usetWord_eq,
              (WordArray.size_uset stkS ((sp - 1).toUSize * Regex.VM.Wide.wordBytes) v0
                (h.wordBound (sp - 1) (Nat.lt_of_lt_of_le hi h.sp_le)
                  (Nat.lt_of_lt_of_le hi h.sp_fit))).2]
            exact hroom)
          (Nat.lt_of_succ_le hfit)))
      (sp + 1) nStates :=
  let hi : sp - 1 < sp := Nat.sub_lt hsp (by decide)
  let hw := h.write (sp - 1) hi v0 hv0
  hw.push
    (by
      rw [WordArray.usetWord_eq,
        (WordArray.size_uset stkS ((sp - 1).toUSize * Regex.VM.Wide.wordBytes) v0
          (h.wordBound (sp - 1) (Nat.lt_of_lt_of_le hi h.sp_le)
            (Nat.lt_of_lt_of_le hi h.sp_fit))).2]
      exact hroom)
    (Nat.lt_of_succ_le hfit) v1 hv1

/-- An empty live prefix on the same buffer. -/
theorem clear (h : StackInv stkS sp nStates) : StackInv stkS 0 nStates :=
  ⟨Nat.zero_le _, Nat.zero_le _, h.div4, fun _ hi => by omega⟩

theorem cast {stkS stkS' : WordArray} {sp sp' n : Nat}
    (h : StackInv stkS sp n) (hs : stkS' = stkS) (hp : sp' = sp) : StackInv stkS' sp' n := by
  subst hs hp
  exact h

/-- Two extra words leave a free slot above the live prefix. -/
theorem grow2_room (h : StackInv stkS sp nStates) :
    sp < ((stkS.push 0).push 0).size := by
  have h1 := WordArray.push_div4 stkS 0 h.div4
  have h2 := WordArray.push_div4 (stkS.push 0) 0 h1.2
  rw [h2.1, h1.1]
  exact Nat.lt_of_le_of_lt h.sp_le (Nat.lt_add_of_pos_right (by decide : 0 < 1 + 1))

/-- An empty live prefix on a word-aligned buffer. -/
theorem empty (stkS : WordArray) (nStates : Nat)
    (hdiv : 4 * stkS.size = stkS.data.size) : StackInv stkS 0 nStates :=
  ⟨Nat.zero_le _, Nat.zero_le _, hdiv, fun _ hi => by omega⟩

/-- A zeroed stack with `start` in slot 0. `nWords * 4 < 2^32` is the allocation length. -/
theorem install (nWords nStates : Nat) (hwords : 0 < nWords)
    (hbytes : nWords * 4 < 2 ^ 32) (start : UInt32) (hstart : start.toNat < nStates) :
    StackInv ((WordArray.zeros nWords).usetWord 0 start
      ((StackInv.empty (WordArray.zeros nWords) nStates
        (WordArray.zeros_spec nWords hbytes).2).wordBound 0
        (by rw [(WordArray.zeros_spec nWords hbytes).1]; exact hwords) (by decide)))
      1 nStates :=
  StackInv.push (StackInv.empty (WordArray.zeros nWords) nStates
      (WordArray.zeros_spec nWords hbytes).2)
    (by rw [(WordArray.zeros_spec nWords hbytes).1]; exact hwords) (by decide) start hstart

/-- Pop one slot and write `v` back into it. Depth stays `sp`. -/
theorem succAt (h : StackInv stkS sp nStates) (hsp : 0 < sp)
    (v : UInt32) (hv : v.toNat < nStates) (sp' : Nat) (heq : sp' = sp - 1)
    (hw : (sp'.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ stkS.data.size) :
    StackInv (stkS.usetWord sp'.toUSize v hw) sp nStates := by
  subst heq
  exact cast (h.stepSucc hsp v hv) (usetWord_rfl rfl rfl) rfl

/--
Write both successors of a `.split`. `v0` replaces the popped slot and `v1` is
pushed above it, so the depth is `sp + 1`.
-/
theorem splitAt (h : StackInv stkS sp nStates) (hsp : 0 < sp)
    (hroom : sp < stkS.size) (hfit : sp + 1 ≤ 2 ^ 30)
    (v0 v1 : UInt32) (hv0 : v0.toNat < nStates) (hv1 : v1.toNat < nStates)
    (sp' : Nat) (heq : sp' = sp - 1)
    (hw0 : (sp'.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ stkS.data.size)
    (hw1 : ((sp' + 1).toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤
      (stkS.usetWord sp'.toUSize v0 hw0).data.size)
    (hidx : (sp' + 1).toUSize = sp.toUSize) :
    StackInv ((stkS.usetWord sp'.toUSize v0 hw0).usetWord (sp' + 1).toUSize v1 hw1)
      (sp + 1) nStates := by
  subst heq
  have h1 := h.succAt hsp v0 hv0 (sp - 1) rfl hw0
  have hroom1 : sp < (stkS.usetWord (sp - 1).toUSize v0 hw0).size := by
    rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
    exact hroom
  have hfitSp : sp < 2 ^ 30 := Nat.lt_of_succ_le hfit
  have hpush := h1.push hroom1 hfitSp v1 hv1
  exact cast hpush
    (usetWord_rfl hidx rfl) rfl

/-- Replace the live prefix by the single state `v` in slot 0. -/
theorem reset (h : StackInv stkS sp nStates) (hroom : 0 < stkS.size)
    (v : UInt32) (hv : v.toNat < nStates) :
    StackInv (stkS.usetWord 0 v (h.wordBound 0 hroom (by decide))) 1 nStates := by
  have hw := h.wordBound 0 hroom (by decide)
  have h0 : (0 : Nat).toUSize = 0 := USize.toNat_inj.mp (by
    rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (by decide),
      Regex.VM.Wide.toNat_uSize_ofNat_of_lt 0 (by decide)])
  have hw' : ((0 : USize) * Regex.VM.Wide.wordBytes).toNat + 4 ≤ stkS.data.size := by
    simpa [h0] using hw
  have hsz := WordArray.size_uset stkS (0 * Regex.VM.Wide.wordBytes) v hw'
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [WordArray.usetWord_eq, hsz.2]
    omega
  · decide
  · rw [WordArray.usetWord_eq, hsz.1, hsz.2]
    exact h.div4
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    have heq : stkS.usetWord (0 : Nat).toUSize v hw =
        stkS.usetWord 0 v (h.wordBound 0 hroom (by decide)) :=
      usetWord_rfl h0 rfl
    rw [← heq, wordAt_usetWord stkS 0 v hw (by decide)]
    exact hv

end StackInv

/--
`state` occurs in the live prefix: the sparse word points at a dense slot that
stores `state`.
-/
def SetMem (den spa : WordArray) (count state : Nat) : Prop :=
  (wordAt spa (4 * state)).toNat < count ∧
    (wordAt den (4 * (wordAt spa (4 * state)).toNat)).toNat = state

/--
Live members of one sparse set.

`count ≤ n` is the set bound. Dense word `i < count` is a state id below `n`,
and the sparse word at that id is `i`. Both arrays have `n` words and are 4-byte
aligned. `n ≤ 2^30` keeps every index inside a 32-bit byte offset. This is the
stock `SparseSet` invariant, read off the word buffers.
-/
structure SetInv (den spa : WordArray) (count n : Nat) : Prop where
  count_le : count ≤ n
  n_fit : n ≤ 2 ^ 30
  den_size : den.size = n
  spa_size : spa.size = n
  den_div4 : 4 * den.size = den.data.size
  spa_div4 : 4 * spa.size = spa.data.size
  dense_lt : ∀ i, i < count → (wordAt den (4 * i)).toNat < n
  sparse_dense : ∀ i, i < count →
    wordAt spa (4 * (wordAt den (4 * i)).toNat) = i.toUInt32

namespace SetInv

variable {den spa : WordArray} {count n : Nat}

private theorem u32 (h : SetInv den spa count n) (i : Nat) (hi : i < n) : i < UInt32.size := by
  simpa [UInt32.size] using
    Nat.lt_trans (Nat.lt_of_lt_of_le hi h.n_fit) (by decide : 2 ^ 30 < 2 ^ 32)

theorem wordBound (h : SetInv den spa count n) (a : WordArray)
    (hsize : a.size = n) (hdiv : 4 * a.size = a.data.size) (i : Nat) (hi : i < n) :
    (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size := by
  have h30 : i < 2 ^ 30 := Nat.lt_of_lt_of_le hi h.n_fit
  have hidx : i < a.size := by rw [hsize]; exact hi
  rw [indexBytes i h30]
  have hmul : 4 * (i + 1) ≤ 4 * a.size := Nat.mul_le_mul_left 4 (Nat.succ_le_of_lt hidx)
  rw [hdiv] at hmul
  omega

theorem denBound (h : SetInv den spa count n) (i : Nat) (hi : i < n) :
    (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ den.data.size :=
  h.wordBound den h.den_size h.den_div4 i hi

theorem spaBound (h : SetInv den spa count n) (i : Nat) (hi : i < n) :
    (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ spa.data.size :=
  h.wordBound spa h.spa_size h.spa_div4 i hi

/-- The state id in dense slot `i`. -/
def dense (h : SetInv den spa count n) (i : Nat) (hi : i < count) : Fin n :=
  ⟨(wordAt den (4 * i)).toNat, h.dense_lt i hi⟩

theorem empty (den spa : WordArray) (n : Nat) (hden : den.size = n) (hspa : spa.size = n)
    (hden4 : 4 * den.size = den.data.size) (hspa4 : 4 * spa.size = spa.data.size)
    (hfit : n ≤ 2 ^ 30) : SetInv den spa 0 n :=
  ⟨Nat.zero_le _, hfit, hden, hspa, hden4, hspa4,
    fun _ hi => by omega, fun _ hi => by omega⟩

/-- A zeroed pair of `n`-word buffers, when the allocation length fits in 32 bits. -/
theorem ofZeros (n : Nat) (hbytes : n * 4 < 2 ^ 32) (hfit : n ≤ 2 ^ 30) :
    SetInv (WordArray.zeros n) (WordArray.zeros n) 0 n :=
  empty _ _ n (WordArray.zeros_spec n hbytes).1 (WordArray.zeros_spec n hbytes).1
    (WordArray.zeros_spec n hbytes).2 (WordArray.zeros_spec n hbytes).2 hfit

/-- Dropping the count clears the set. The arrays are left as they are. -/
theorem clear (h : SetInv den spa count n) : SetInv den spa 0 n :=
  empty den spa n h.den_size h.spa_size h.den_div4 h.spa_div4 h.n_fit

theorem mem_of_full (h : SetInv den spa count n) (heq : count = n) (state : Nat)
    (hs : state < n) : SetMem den spa count state := by
  let f : Fin n → Fin n := fun i =>
    ⟨(wordAt den (4 * i.val)).toNat, h.dense_lt i.val (heq.symm ▸ i.isLt)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have ha := h.sparse_dense a.val (heq.symm ▸ a.isLt)
    have hb := h.sparse_dense b.val (heq.symm ▸ b.isLt)
    have hdenEq : (wordAt den (4 * a.val)).toNat = (wordAt den (4 * b.val)).toNat := by
      simpa [f] using congrArg (fun x : Fin n => (x : Nat)) hab
    have hwords : a.val.toUInt32 = b.val.toUInt32 := by
      rw [← ha, ← hb]
      exact congrArg (fun k => wordAt spa (4 * k)) hdenEq
    have haval : a.val = b.val := by
      rw [← toNat_toUInt32_of_lt (u32 h a.val a.isLt), ← toNat_toUInt32_of_lt (u32 h b.val b.isLt)]
      exact congrArg UInt32.toNat hwords
    exact Fin.ext haval
  rcases Regex.Data.SparseSet.Bijection.surj_of_inj f hinj ⟨state, hs⟩ with ⟨i, hi⟩
  have hdense : (wordAt den (4 * i.val)).toNat = state := congrArg Fin.val hi
  have hsp := h.sparse_dense i.val (heq.symm ▸ i.isLt)
  have hread : wordAt spa (4 * state) = i.val.toUInt32 := by
    simpa [hdense] using hsp
  refine ⟨?_, ?_⟩
  · rw [hread, toNat_toUInt32_of_lt (u32 h i.val i.isLt), heq]
    exact i.isLt
  · rw [hread, toNat_toUInt32_of_lt (u32 h i.val i.isLt)]
    exact hdense

/-- A missing state still has a free dense slot. -/
theorem lt_of_not_mem (h : SetInv den spa count n) (state : Nat) (hs : state < n)
    (hnot : ¬ SetMem den spa count state) : count < n := by
  cases Nat.lt_or_ge count n with
  | inl hlt => exact hlt
  | inr hge => exact False.elim (hnot (mem_of_full h (Nat.le_antisymm h.count_le hge) state hs))

private theorem slotBytes (h : SetInv den spa count n) (a : WordArray)
    (hsize : a.size = n) (hdiv : 4 * a.size = a.data.size) (i : Nat) (hi : i < n) :
    4 * i + 4 ≤ a.data.size := by
  have hb := h.wordBound a hsize hdiv i hi
  rw [indexBytes i (Nat.lt_of_lt_of_le hi h.n_fit)] at hb
  exact hb

/--
Insert `state` at the end of the live prefix. `state` is not already a member,
so the previous `sparse[dense i] = i` equations stay put.
-/
theorem insert (h : SetInv den spa count n) (state : Nat) (hs : state < n)
    (hnot : ¬ SetMem den spa count state) :
    SetInv (den.usetWord count.toUSize state.toUInt32
        (h.denBound count (lt_of_not_mem h state hs hnot)))
      (spa.usetWord state.toUSize count.toUInt32 (h.spaBound state hs)) (count + 1) n := by
  have hroom : count < n := lt_of_not_mem h state hs hnot
  have hdenB := h.denBound count hroom
  have hspaB := h.spaBound state hs
  have hcount30 : count < 2 ^ 30 := Nat.lt_of_lt_of_le hroom h.n_fit
  have hstate30 : state < 2 ^ 30 := Nat.lt_of_lt_of_le hs h.n_fit
  have hdenSz := WordArray.size_uset den (count.toUSize * Regex.VM.Wide.wordBytes) state.toUInt32 hdenB
  have hspaSz := WordArray.size_uset spa (state.toUSize * Regex.VM.Wide.wordBytes) count.toUInt32 hspaB
  refine ⟨?_, h.n_fit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hroom
  · rw [WordArray.usetWord_eq, hdenSz.2]; exact h.den_size
  · rw [WordArray.usetWord_eq, hspaSz.2]; exact h.spa_size
  · rw [WordArray.usetWord_eq, hdenSz.1, hdenSz.2]; exact h.den_div4
  · rw [WordArray.usetWord_eq, hspaSz.1, hspaSz.2]; exact h.spa_div4
  · intro i hi
    by_cases hie : i = count
    · subst i
      rw [wordAt_usetWord _ _ _ hdenB hcount30, toNat_toUInt32_of_lt (u32 h state hs)]
      exact hs
    · have hi' : i < count := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hie
      have hi30 : i < 2 ^ 30 := Nat.lt_of_lt_of_le hi' (Nat.le_trans h.count_le h.n_fit)
      rw [wordAt_usetWord_ne _ _ _ _ hdenB hcount30 hi30 (Ne.symm hie)
        (slotBytes h den h.den_size h.den_div4 i (Nat.lt_of_lt_of_le hi' h.count_le))]
      exact h.dense_lt i hi'
  · intro i hi
    by_cases hie : i = count
    · subst i
      rw [wordAt_usetWord _ _ _ hdenB hcount30, toNat_toUInt32_of_lt (u32 h state hs)]
      exact wordAt_usetWord _ _ _ hspaB hstate30
    · have hi' : i < count := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hie
      have hi30 : i < 2 ^ 30 := Nat.lt_of_lt_of_le hi' (Nat.le_trans h.count_le h.n_fit)
      have hold := h.dense_lt i hi'
      have hsame := wordAt_usetWord_ne den count i state.toUInt32 hdenB hcount30 hi30 (Ne.symm hie)
        (slotBytes h den h.den_size h.den_div4 i (Nat.lt_of_lt_of_le hi' h.count_le))
      have hid : (wordAt den (4 * i)).toNat < n := hold
      have hid30 : (wordAt den (4 * i)).toNat < 2 ^ 30 := Nat.lt_of_lt_of_le hid h.n_fit
      have hne : state ≠ (wordAt den (4 * i)).toNat := by
        intro heqId
        apply hnot
        have hsp := h.sparse_dense i hi'
        have hread : wordAt spa (4 * state) = i.toUInt32 := by simpa [heqId] using hsp
        refine ⟨?_, ?_⟩
        · rw [hread, toNat_toUInt32_of_lt (u32 h i (Nat.lt_of_lt_of_le hi' h.count_le))]
          exact hi'
        · rw [hread, toNat_toUInt32_of_lt (u32 h i (Nat.lt_of_lt_of_le hi' h.count_le))]
          exact heqId.symm
      rw [hsame]
      have hspaSame := wordAt_usetWord_ne spa state (wordAt den (4 * i)).toNat count.toUInt32 hspaB
        hstate30 hid30 hne
        (slotBytes h spa h.spa_size h.spa_div4 _ hid)
      rw [hspaSame]
      exact h.sparse_dense i hi'

/-- The state just inserted is a member at the new top slot. -/
theorem mem_insert (h : SetInv den spa count n) (state : Nat) (hs : state < n)
    (hnot : ¬ SetMem den spa count state) :
    SetMem (den.usetWord count.toUSize state.toUInt32
        (h.denBound count (lt_of_not_mem h state hs hnot)))
      (spa.usetWord state.toUSize count.toUInt32 (h.spaBound state hs)) (count + 1) state := by
  have hroom : count < n := lt_of_not_mem h state hs hnot
  have hdenB := h.denBound count hroom
  have hspaB := h.spaBound state hs
  have hcount30 : count < 2 ^ 30 := Nat.lt_of_lt_of_le hroom h.n_fit
  have hstate30 : state < 2 ^ 30 := Nat.lt_of_lt_of_le hs h.n_fit
  have hread : wordAt (spa.usetWord state.toUSize count.toUInt32 hspaB) (4 * state) =
      count.toUInt32 :=
    wordAt_usetWord _ _ _ hspaB hstate30
  refine ⟨?_, ?_⟩
  · rw [hread, toNat_toUInt32_of_lt (u32 h count hroom)]
    exact Nat.lt_succ_self count
  · rw [hread, toNat_toUInt32_of_lt (u32 h count hroom),
      wordAt_usetWord _ _ _ hdenB hcount30, toNat_toUInt32_of_lt (u32 h state hs)]

end SetInv

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
Flat program the hot loop is allowed to read.

`n * 12 ≤ 2^32` is the `ofNFA` window. Every `next` word is a state id, a `.split`
extra word is a state id, and a `.sparse` extra word indexes `classes`.
-/
structure WordsWf (words : WordArray) (classes : Array ClassTable) (n : Nat) : Prop where
  n_pos : 0 < n
  n_bytes : n * 12 ≤ 2 ^ 32
  data_size : words.data.size = 12 * n
  next_lt : ∀ j, j < n → (wordAt words (12 * j + 4)).toNat < n
  split_lt : ∀ j, j < n → wordAt words (12 * j) = tagSplit →
    (wordAt words (12 * j + 8)).toNat < n
  sparse_lt : ∀ j, j < n → wordAt words (12 * j) = tagSparse →
    (wordAt words (12 * j + 8)).toNat < classes.size

theorem WordsWf.le_30 {words : WordArray} {classes : Array ClassTable} {n : Nat}
    (h : WordsWf words classes n) : n ≤ 2 ^ 30 := by
  have hdiv : n ≤ 2 ^ 32 / 12 := (Nat.le_div_iff_mul_le (by decide : 0 < 12)).mpr h.n_bytes
  exact Nat.le_trans hdiv (by decide : 2 ^ 32 / 12 ≤ 2 ^ 30)

/-- Capture rows and the ε-stack rows inside one flat buffer. -/
structure EvalBuf (caps : ByteArray) (stkS : WordArray) (slots cRow0 nRow0 stackRow0 : USize)
    (nSlots n : Nat) : Prop where
  slots_eq : slots.toNat = nSlots
  c_row : cRow0.toNat = 2 ∨ cRow0.toNat = 2 + n
  n_row : nRow0.toNat = 2 ∨ nRow0.toNat = 2 + n
  rows_ne : cRow0.toNat ≠ nRow0.toNat
  stack_row : stackRow0.toNat = 2 + 2 * n
  /-- `n + 2` words cover a live prefix of height at most `n + 1`. -/
  stk_ge : n + 2 ≤ stkS.size
  rows_size : (2 + 2 * n + stkS.size) * nSlots * 8 ≤ caps.size
  rows_fit : (2 + 2 * n + stkS.size) * nSlots * 8 ≤ 2 ^ 32

/-- Where saves and anchors read the input, relative to the stepping position. -/
def CpRel {s : String} (phase : UInt32) (p cp : Pos s) : Prop :=
  (phase = phaseClosure → cp = p) ∧
  (phase = phaseStepClosure → cp.remainingBytes < p.remainingBytes)

/--
Invariants of one `eval` iteration.

`sp ≤ nCount + 1` bounds the ε-stack by the states still to be visited, which is
what makes closure fuel decrease on `.split`. `i ≤ cCount` keeps the step loop
from walking past the dense prefix.
-/
structure RunInv {s : String}
    (words : WordArray) (classes : Array ClassTable) (start : UInt32)
    (nSlots : Nat) (nStates : UInt32) (slots : USize)
    (cRow0 nRow0 stackRow0 : USize)
    (p cp : Pos s)
    (cCount : UInt32) (cDen cSpa : WordArray)
    (nCount : UInt32) (nDen nSpa : WordArray)
    (stkS : WordArray) (caps : ByteArray) (sp : Nat)
    (phase i : UInt32) : Prop where
  words : WordsWf words classes nStates.toNat
  start_lt : start.toNat < nStates.toNat
  curr : SetInv cDen cSpa cCount.toNat nStates.toNat
  next : SetInv nDen nSpa nCount.toNat nStates.toNat
  stack : StackInv stkS sp nStates.toNat
  buf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat
  i_le : i.toNat ≤ cCount.toNat
  sp_le : sp ≤ nCount.toNat + 1
  phase_ok : phase = phaseClosure ∨ phase = phaseStepClosure ∨ phase = phaseStep
  cp_rel : CpRel phase p cp
  step_i : phase = phaseStepClosure → i.toNat < cCount.toNat

private theorem u32_usize (w : UInt32) : w.toUSize = w.toNat.toUSize := by
  apply USize.toNat_inj.mp
  rw [UInt32.toNat_toUSize, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (UInt32.toNat_lt w)]

private theorem toNat_u32_one : (1 : UInt32).toNat = 1 :=
  UInt32.toNat_ofNat_of_lt (by decide : 1 < UInt32.size)

private theorem toNat_u32_add_one {a : UInt32} (h : a.toNat + 1 < 2 ^ 32) :
    (a + 1).toNat = a.toNat + 1 := by
  rw [UInt32.toNat_add, toNat_u32_one]
  exact Nat.mod_eq_of_lt h

private theorem stride_toNat : strideBytes.toNat = 12 :=
  Regex.VM.Wide.toNat_uSize_ofNat_of_lt 12 (by decide)

private theorem usize_mul_toNat (a b : USize) (h : a.toNat * b.toNat < 2 ^ 32) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [USize.toNat_mul]
  exact Nat.mod_eq_of_lt (Regex.VM.Wide.lt_two_pow_numBits_of_lt_2_pow_32 h)

private theorem usize_add_toNat (a b : USize) (h : a.toNat + b.toNat < 2 ^ 32) :
    (a + b).toNat = a.toNat + b.toNat := by
  rw [USize.toNat_add]
  exact Nat.mod_eq_of_lt (Regex.VM.Wide.lt_two_pow_numBits_of_lt_2_pow_32 h)

private theorem mul_stride_toNat (state : UInt32) (h : state.toNat * 12 < 2 ^ 32) :
    (state.toUSize * strideBytes).toNat = state.toNat * 12 := by
  rw [usize_mul_toNat _ _ (by rw [UInt32.toNat_toUSize, stride_toNat]; exact h),
    UInt32.toNat_toUSize, stride_toNat]

private theorem ugetWord_wordAt (a : WordArray) (i : UInt32)
    (h : (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size)
    (hi : i.toNat < 2 ^ 30) :
    a.ugetWord i.toUSize h = wordAt a (4 * i.toNat) := by
  rw [WordArray.ugetWord]
  have hidx : i.toUSize * Regex.VM.Wide.wordBytes = (4 * i.toNat).toUSize := by
    rw [u32_usize i]
    exact wordIndex i.toNat hi
  have hnat : 4 * i.toNat + 4 ≤ a.data.size := by
    have hb := h
    rw [u32_usize i, indexBytes i.toNat hi] at hb
    exact hb
  have h32 : 4 * i.toNat < 2 ^ 32 := by omega
  rw [wordAt_eq a (4 * i.toNat) hnat h32]
  exact WordArray.uget_off_eq a _ _ h
    (by
      rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]
      exact hnat) hidx

private theorem state_byte_lt {n : Nat} (hbytes : n * 12 ≤ 2 ^ 32) {state : Nat}
    (hs : state < n) (k : Nat) (hk : k < 12) : state * 12 + k < 2 ^ 32 := by
  have : state * 12 + 12 ≤ n * 12 := by
    have : state + 1 ≤ n := Nat.succ_le_of_lt hs
    omega
  omega

private theorem WordsWf.baseNat {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n) :
    (state.toUSize * strideBytes).toNat = state.toNat * 12 :=
  mul_stride_toNat state (state_byte_lt h.n_bytes hs 0 (by decide))

private theorem WordsWf.tagBound {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n) :
    (state.toUSize * strideBytes).toNat + 4 ≤ words.data.size := by
  rw [h.baseNat state hs, h.data_size]
  have : state.toNat + 1 ≤ n := Nat.succ_le_of_lt hs
  omega

private theorem WordsWf.offBound {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n) (k : USize) (hk : k.toNat ≤ 8) :
    ((state.toUSize * strideBytes) + k).toNat + 4 ≤ words.data.size ∧
      ((state.toUSize * strideBytes) + k).toNat = state.toNat * 12 + k.toNat := by
  have hbase := h.baseNat state hs
  have hsum : (state.toUSize * strideBytes).toNat + k.toNat < 2 ^ 32 := by
    rw [hbase]
    exact state_byte_lt h.n_bytes hs k.toNat (by omega)
  refine ⟨?_, ?_⟩
  · rw [usize_add_toNat _ _ hsum, hbase, h.data_size]
    have : state.toNat + 1 ≤ n := Nat.succ_le_of_lt hs
    omega
  · rw [usize_add_toNat _ _ hsum, hbase]

private theorem WordsWf.tag_eq {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n)
    (hb : (state.toUSize * strideBytes).toNat + 4 ≤ words.data.size) :
    words.uget (state.toUSize * strideBytes) hb = wordAt words (12 * state.toNat) := by
  have hbase := h.baseNat state hs
  have hcomm : state.toNat * 12 = 12 * state.toNat := Nat.mul_comm _ _
  have h32 : 12 * state.toNat < 2 ^ 32 := by
    rw [← hcomm]
    exact state_byte_lt h.n_bytes hs 0 (by decide)
  have hnat : 12 * state.toNat + 4 ≤ words.data.size := by
    rw [← hcomm, h.data_size]
    have : state.toNat + 1 ≤ n := Nat.succ_le_of_lt hs
    omega
  rw [wordAt_eq words (12 * state.toNat) hnat h32]
  apply WordArray.uget_off_eq
  apply USize.toNat_inj.mp
  rw [hbase, hcomm, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]

private theorem WordsWf.word_eq {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n) (k : USize) (hk : k.toNat = 4 ∨ k.toNat = 8)
    (hb : ((state.toUSize * strideBytes) + k).toNat + 4 ≤ words.data.size) :
    words.uget ((state.toUSize * strideBytes) + k) hb =
      wordAt words (12 * state.toNat + k.toNat) := by
  obtain ⟨_, hadd⟩ := h.offBound state hs k (by cases hk <;> omega)
  have hcomm : state.toNat * 12 = 12 * state.toNat := Nat.mul_comm _ _
  have h32 : 12 * state.toNat + k.toNat < 2 ^ 32 := by
    rw [← hcomm, ← hadd]
    have hb4 := hb
    rw [h.data_size] at hb4
    have hn : 12 * n ≤ 2 ^ 32 := by
      rw [Nat.mul_comm]
      exact h.n_bytes
    omega
  have hnat : 12 * state.toNat + k.toNat + 4 ≤ words.data.size := by
    rw [← hcomm, ← hadd]
    exact hb
  rw [wordAt_eq words (12 * state.toNat + k.toNat) hnat h32]
  apply WordArray.uget_off_eq
  apply USize.toNat_inj.mp
  rw [hadd, hcomm, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]

namespace EvalBuf

variable {caps stkS : _} {slots cRow0 nRow0 stackRow0 : USize} {nSlots n : Nat}

theorem swap (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n) :
    EvalBuf caps stkS slots nRow0 cRow0 stackRow0 nSlots n where
  slots_eq := h.slots_eq
  c_row := h.n_row
  n_row := h.c_row
  rows_ne := Ne.symm h.rows_ne
  stack_row := h.stack_row
  stk_ge := h.stk_ge
  rows_size := h.rows_size
  rows_fit := h.rows_fit

theorem of_size {caps' : ByteArray} {stkS' : WordArray}
    (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (hcaps : caps'.size = caps.size) (hstk : stkS'.size = stkS.size) :
    EvalBuf caps' stkS' slots cRow0 nRow0 stackRow0 nSlots n where
  slots_eq := h.slots_eq
  c_row := h.c_row
  n_row := h.n_row
  rows_ne := h.rows_ne
  stack_row := h.stack_row
  stk_ge := by rw [hstk]; exact h.stk_ge
  rows_size := by rw [hcaps, hstk]; exact h.rows_size
  rows_fit := by rw [hstk]; exact h.rows_fit

private theorem rowCount_le (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (hpos : 0 < nSlots) : 2 + 2 * n + stkS.size ≤ 2 ^ 32 := by
  have hmul : (2 + 2 * n + stkS.size) * (nSlots * 8) ≤ 2 ^ 32 := by
    rw [← Nat.mul_assoc]
    exact h.rows_fit
  have h8 : 0 < nSlots * 8 := by omega
  exact Nat.le_trans ((Nat.le_div_iff_mul_le h8).mpr hmul) (Nat.div_le_self _ _)

theorem window (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (row : USize) (r : Nat) (hidx : nSlots = 0 ∨ row.toNat = r)
    (hlt : r < 2 + 2 * n + stkS.size) :
    (rowOff row slots).toNat + slots.toNat * 8 ≤ caps.size ∧
      (rowOff row slots).toNat + slots.toNat * 8 ≤ 2 ^ 32 := by
  cases Nat.eq_zero_or_pos nSlots with
  | inl h0 =>
    have hslots : slots = 0 := by
      apply USize.toNat_inj.mp
      rw [h.slots_eq, h0, USize.toNat_zero]
    rw [hslots, rowOff_slots_zero, USize.toNat_zero]
    exact ⟨Nat.zero_le _, Nat.zero_le _⟩
  | inr hpos =>
    have hr : row.toNat = r := by
      cases hidx with
      | inl hz => exact absurd hz (Nat.ne_of_gt hpos)
      | inr hr => exact hr
    have hend : (r + 1) * nSlots * 8 ≤ (2 + 2 * n + stkS.size) * nSlots * 8 := by
      have hr1 : r + 1 ≤ 2 + 2 * n + stkS.size := Nat.succ_le_of_lt hlt
      exact Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right nSlots hr1)
    have hsplit : (r + 1) * nSlots * 8 = r * nSlots * 8 + nSlots * 8 := by
      rw [Nat.succ_mul, Nat.add_mul]
    have hstrict : r * nSlots * 8 < 2 ^ 32 := by
      have hle : r * nSlots * 8 + nSlots * 8 ≤ 2 ^ 32 :=
        Nat.le_trans (by rw [← hsplit]; exact hend) h.rows_fit
      exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega : 0 < nSlots * 8)) hle
    have hoff : (rowOff row slots).toNat = r * nSlots * 8 := by
      rw [rowOff_toNat row slots (by rw [hr, h.slots_eq]; exact hstrict), hr, h.slots_eq]
    rw [hoff, h.slots_eq]
    exact ⟨by rw [← hsplit]; exact Nat.le_trans hend h.rows_size,
      by rw [← hsplit]; exact Nat.le_trans hend h.rows_fit⟩

theorem indexNat (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (base idx : USize) (b k : Nat) (hb : base.toNat = b) (hk : idx.toNat = k)
    (hlt : b + k < 2 + 2 * n + stkS.size) :
    nSlots = 0 ∨ (base + idx).toNat = b + k := by
  cases Nat.eq_zero_or_pos nSlots with
  | inl hz => exact Or.inl hz
  | inr hp =>
    refine Or.inr ?_
    have hsum : b + k < 2 ^ 32 := Nat.lt_of_lt_of_le hlt (h.rowCount_le hp)
    rw [usize_add_toNat base idx (by rw [hb, hk]; exact hsum), hb, hk]

theorem slotBound (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (row : USize) (r : Nat) (hidx : nSlots = 0 ∨ row.toNat = r)
    (hlt : r < 2 + 2 * n + stkS.size) (extra : UInt32) (he : extra.toNat < nSlots) :
    ((rowOff row slots) + extra.toUSize * slotBytes).toNat + 8 ≤ caps.size := by
  have hpos : 0 < nSlots := Nat.lt_of_le_of_lt (Nat.zero_le _) he
  have hr : row.toNat = r := by
    cases hidx with
    | inl hz => exact absurd hz (Nat.ne_of_gt hpos)
    | inr hr => exact hr
  have hw := h.window row r hidx hlt
  have h8 : slotBytes.toNat = 8 :=
    Regex.VM.Wide.toNat_uSize_ofNat_of_lt 8 (by decide)
  have hex8 : extra.toNat * 8 < 2 ^ 32 := by
    have hone : 1 ≤ 2 + 2 * n + stkS.size := by omega
    have hmul := Nat.mul_le_mul_right (nSlots * 8) hone
    have hwide : nSlots * 8 ≤ (2 + 2 * n + stkS.size) * nSlots * 8 := by
      rw [Nat.one_mul, ← Nat.mul_assoc] at hmul
      exact hmul
    have hle : extra.toNat * 8 + 8 ≤ nSlots * 8 := by
      have hmul' := Nat.mul_le_mul_right 8 (Nat.succ_le_of_lt he)
      rwa [Nat.succ_mul] at hmul'
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8))
      (Nat.le_trans hle (Nat.le_trans hwide h.rows_fit))
  have hex : (extra.toUSize * slotBytes).toNat = extra.toNat * 8 := by
    rw [usize_mul_toNat _ _ (by rw [UInt32.toNat_toUSize, h8]; exact hex8),
      UInt32.toNat_toUSize, h8]
  have hsplit : (r + 1) * nSlots * 8 = r * nSlots * 8 + nSlots * 8 := by
    rw [Nat.succ_mul, Nat.add_mul]
  have hstrict : r * nSlots * 8 < 2 ^ 32 := by
    have hend : (r + 1) * nSlots * 8 ≤ (2 + 2 * n + stkS.size) * nSlots * 8 :=
      Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right nSlots (Nat.succ_le_of_lt hlt))
    have hle : r * nSlots * 8 + nSlots * 8 ≤ 2 ^ 32 :=
      Nat.le_trans (by rw [← hsplit]; exact hend) h.rows_fit
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by omega : 0 < nSlots * 8)) hle
  have hrow : (rowOff row slots).toNat = r * nSlots * 8 := by
    rw [rowOff_toNat row slots (by rw [hr, h.slots_eq]; exact hstrict), hr, h.slots_eq]
  have hsum : (rowOff row slots).toNat + extra.toNat * 8 < 2 ^ 32 := by
    rw [hrow]
    have hle : r * nSlots * 8 + extra.toNat * 8 + 8 ≤ 2 ^ 32 := by
      have hmul := Nat.mul_le_mul_right 8 (Nat.succ_le_of_lt he)
      rw [Nat.succ_mul] at hmul
      have hrest : r * nSlots * 8 + (extra.toNat * 8 + 8) ≤ r * nSlots * 8 + nSlots * 8 :=
        Nat.add_le_add_left hmul _
      have hend : r * nSlots * 8 + nSlots * 8 ≤ 2 ^ 32 := by
        rw [← hsplit]
        exact Nat.le_trans
          (Nat.mul_le_mul_right 8 (Nat.mul_le_mul_right nSlots (Nat.succ_le_of_lt hlt))) h.rows_fit
      exact Nat.le_trans (by rw [Nat.add_assoc]; exact hrest) hend
    exact Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) hle
  rw [usize_add_toNat _ _ (by rw [hex]; exact hsum), hex, hrow]
  have hmul := Nat.mul_le_mul_right 8 (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hmul
  have hrest : r * nSlots * 8 + (extra.toNat * 8 + 8) ≤ r * nSlots * 8 + nSlots * 8 :=
    Nat.add_le_add_left hmul _
  have hsize := hw.1
  rw [h.slots_eq, hrow, ← hsplit] at hsize
  exact Nat.le_trans (by rw [Nat.add_assoc]; exact hrest) (by rw [← hsplit]; exact hsize)

/-- `base + state` stays inside the capture rows when `base` is a current or next row. -/
theorem addU32 (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (base : USize) (hb : base.toNat = 2 ∨ base.toNat = 2 + n)
    (state : UInt32) (hs : state.toNat < n) :
    (nSlots = 0 ∨ (base + state.toUSize).toNat = base.toNat + state.toNat) ∧
      base.toNat + state.toNat < 2 + 2 * n + stkS.size := by
  refine ⟨h.indexNat base state.toUSize base.toNat state.toNat rfl (UInt32.toNat_toUSize state) ?_, ?_⟩
  all_goals rcases hb with hr | hr <;> rw [hr] <;> omega

/-- Stack slot `k` lies under the live stack rows. -/
theorem stackSlot (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (k : Nat) (hk : k < stkS.size) (hk32 : k < 2 ^ 32) :
    (nSlots = 0 ∨ (stackRow0 + k.toUSize).toNat = 2 + 2 * n + k) ∧
      2 + 2 * n + k < 2 + 2 * n + stkS.size := by
  refine ⟨h.indexNat stackRow0 k.toUSize (2 + 2 * n) k h.stack_row
      (Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hk32) ?_, ?_⟩
  · omega
  · omega

end EvalBuf

namespace SetInv

theorem insertU32 {den spa : WordArray} {count : UInt32} {n : Nat}
    (h : SetInv den spa count.toNat n) (state : UInt32) (hs : state.toNat < n)
    (hnot : ¬ SetMem den spa count.toNat state.toNat)
    (hcnt : count.toNat + 1 < 2 ^ 32) :
    SetInv (den.usetWord count.toUSize state (by
        rw [u32_usize count]
        exact h.denBound count.toNat (lt_of_not_mem h state.toNat hs hnot)))
      (spa.usetWord state.toUSize count (by
        rw [u32_usize state]
        exact h.spaBound state.toNat hs))
      (count + 1).toNat n := by
  have hdenB := h.denBound count.toNat (lt_of_not_mem h state.toNat hs hnot)
  have hspaB := h.spaBound state.toNat hs
  have hdenU : (count.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ den.data.size := by
    rw [u32_usize count]
    exact hdenB
  have hspaU : (state.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ spa.data.size := by
    rw [u32_usize state]
    exact hspaB
  have hdenEq : den.usetWord count.toUSize state hdenU =
      den.usetWord count.toNat.toUSize state.toNat.toUInt32 hdenB :=
    usetWord_rfl (u32_usize count) (UInt32.ofNat_toNat).symm
  have hspaEq : spa.usetWord state.toUSize count hspaU =
      spa.usetWord state.toNat.toUSize count.toNat.toUInt32 hspaB :=
    usetWord_rfl (u32_usize state) (UInt32.ofNat_toNat).symm
  rw [hdenEq, hspaEq, toNat_u32_add_one hcnt]
  exact insert h state.toNat hs hnot

end SetInv

/-- `1` while the closure is still the one started at the current position. -/
private def phaseRank (phase : UInt32) : Nat :=
  if phase = phaseClosure then 1 else 0

/--
Fuel for the ε-stack. A stepping phase sits strictly above every closure, so
entering a step-closure decreases the measure without moving `p`.
-/
private def closureFuel (phase : UInt32) (sp nCount n : Nat) : Nat :=
  if phase = phaseStep then
    3 * n + 2
  else
    sp + 2 * (n - nCount)

private def evalMeasure {s : String} (p : Pos s) (phase : UInt32) (cCount i : UInt32)
    (sp nCount n : Nat) : Nat × Nat × Nat × Nat :=
  (p.remainingBytes, phaseRank phase, cCount.toNat - i.toNat, closureFuel phase sp nCount n)

private theorem rem_next {s : String} {p : Pos s} (h : p ≠ s.endPos) :
    (p.next h).remainingBytes < p.remainingBytes :=
  (Pos.lt_iff_remainingBytes_lt p (p.next h)).mp p.lt_next

private abbrev EvalRel :=
  Prod.Lex (fun a b : Nat => a < b)
    (Prod.Lex (fun a b : Nat => a < b)
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)))

private theorem lex4_1 {a a' : Nat} {b b' c c' d d' : Nat} (h : a' < a) :
    EvalRel (a', b', c', d') (a, b, c, d) :=
  Prod.Lex.left (b', c', d') (b, c, d) h

private theorem lex4_2 {a b b' : Nat} {c c' d d' : Nat} (h : b' < b) :
    EvalRel (a, b', c', d') (a, b, c, d) :=
  Prod.Lex.right a (Prod.Lex.left (c', d') (c, d) h)

private theorem lex4_3 {a b c c' d d' : Nat} (h : c' < c) :
    EvalRel (a, b, c', d') (a, b, c, d) :=
  Prod.Lex.right a (Prod.Lex.right b (Prod.Lex.left d' d h))

private theorem lex4_4 {a b c d d' : Nat} (h : d' < d) :
    EvalRel (a, b, c, d') (a, b, c, d) :=
  Prod.Lex.right a (Prod.Lex.right b (Prod.Lex.right c h))

private theorem phase_beq_step (phase : UInt32) :
    (phase == phaseStep) = true ↔ phase = phaseStep := by
  simp [beq_iff_eq]

private theorem closureFuel_notStep {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) :
    closureFuel phase sp nCount n = sp + 2 * (n - nCount) := by
  simp [closureFuel, h]

private theorem fuel_pop {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hsp : 0 < sp) :
    closureFuel phase (sp - 1) nCount n < closureFuel phase sp nCount n := by
  rw [closureFuel_notStep h, closureFuel_notStep h]
  omega

private theorem fuel_keep {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hc : nCount < n) :
    closureFuel phase sp (nCount + 1) n < closureFuel phase sp nCount n := by
  rw [closureFuel_notStep h, closureFuel_notStep h]
  omega

private theorem fuel_split {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hc : nCount < n) :
    closureFuel phase (sp + 1) (nCount + 1) n < closureFuel phase sp nCount n := by
  rw [closureFuel_notStep h, closureFuel_notStep h]
  omega

/-- A popped state that is not pushed back, after it has been inserted. -/
private theorem fuel_discard {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hsp : 0 < sp) (hc : nCount < n) :
    closureFuel phase (sp - 1) (nCount + 1) n < closureFuel phase sp nCount n := by
  rw [closureFuel_notStep h, closureFuel_notStep h]
  omega

private theorem fuel_enter (nCount n : Nat) (hc : nCount ≤ n) :
    closureFuel phaseStepClosure 1 nCount n < closureFuel phaseStep 0 nCount n := by
  have hne : phaseStepClosure ≠ phaseStep := by decide
  have hlt : 1 + 2 * (n - nCount) < 3 * n + 2 := by omega
  calc
    closureFuel phaseStepClosure 1 nCount n = 1 + 2 * (n - nCount) := by
      simp [closureFuel, hne]
    _ < 3 * n + 2 := hlt
    _ = closureFuel phaseStep 0 nCount n := by
      simp [closureFuel]

private theorem step_sub_succ {c i : UInt32} (h : i.toNat < c.toNat) :
    c.toNat - (i + 1).toNat < c.toNat - i.toNat := by
  have hsucc : (i + 1).toNat = i.toNat + 1 :=
    toNat_u32_add_one (by
      have := UInt32.toNat_lt c
      omega)
  rw [hsucc]
  exact Nat.sub_succ_lt_self _ _ h

private theorem rank_closure : phaseRank phaseClosure = 1 := by
  unfold phaseRank
  decide

private theorem rank_step : phaseRank phaseStep = 0 := by
  unfold phaseRank
  decide

private theorem rank_stepClosure : phaseRank phaseStepClosure = 0 := by
  unfold phaseRank
  decide

private theorem dec_rem {s : String} {p p' : Pos s} {phase phase' : UInt32}
    {cCount cCount' i i' : UInt32} {sp sp' nCount nCount' n : Nat}
    (h : p'.remainingBytes < p.remainingBytes) :
    EvalRel (evalMeasure p' phase' cCount' i' sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  unfold evalMeasure
  exact lex4_1 h

private theorem dec_rank {s : String} {p q : Pos s} {phase phase' : UInt32}
    {cCount cCount' i i' : UInt32} {sp sp' nCount nCount' n : Nat}
    (hq : q = p) (h : phaseRank phase' < phaseRank phase) :
    EvalRel (evalMeasure q phase' cCount' i' sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  subst hq
  unfold evalMeasure
  exact lex4_2 h

private theorem dec_step {s : String} {p : Pos s} {phase : UInt32}
    {cCount i i' : UInt32} {sp sp' nCount nCount' n : Nat}
    (h : cCount.toNat - i'.toNat < cCount.toNat - i.toNat) :
    EvalRel (evalMeasure p phase cCount i' sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  unfold evalMeasure
  exact lex4_3 h

/-- Step-closure gave up: `i` advances and the phase returns to stepping. Both ranks are `0`. -/
private theorem dec_resume {s : String} {p : Pos s} {cCount i : UInt32}
    {sp sp' nCount nCount' n : Nat}
    (h : cCount.toNat - (i + 1).toNat < cCount.toNat - i.toNat) :
    EvalRel (evalMeasure p phaseStep cCount (i + 1) sp' nCount' n)
      (evalMeasure p phaseStepClosure cCount i sp nCount n) := by
  unfold evalMeasure phaseRank
  exact lex4_3 h

private theorem dec_fuel {s : String} {p : Pos s} {phase : UInt32} {cCount i : UInt32}
    {sp sp' nCount nCount' n : Nat}
    (h : closureFuel phase sp' nCount' n < closureFuel phase sp nCount n) :
    EvalRel (evalMeasure p phase cCount i sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  unfold evalMeasure
  exact lex4_4 h

private theorem fuel_enter_at (sp nCount n : Nat) (hc : nCount ≤ n) :
    closureFuel phaseStepClosure 1 nCount n < closureFuel phaseStep sp nCount n := by
  have hne : ¬ phaseStepClosure = phaseStep := by decide
  have hlt := fuel_enter nCount n hc
  rw [closureFuel_notStep hne] at hlt
  rw [closureFuel_notStep hne]
  simpa [closureFuel] using hlt

private theorem u32_toNat_ne {a b : UInt32} (h : ¬ a = b) : a.toNat ≠ b.toNat := by
  intro heq
  exact h (UInt32.toNat_inj.mp heq)

private theorem phase_stepClosure_of (phase : UInt32)
    (h : phase = phaseClosure ∨ phase = phaseStepClosure ∨ phase = phaseStep)
    (hnot : ¬ phase = phaseStep) (hnotC : ¬ phase = phaseClosure) :
    phase = phaseStepClosure := by
  rcases h with h | h | h
  · exact absurd h hnotC
  · exact h
  · exact absurd h hnot

private theorem CpRel.closure {s : String} (p : Pos s) : CpRel phaseClosure p p :=
  ⟨fun _ => rfl, fun h => absurd h (by decide : phaseClosure ≠ phaseStepClosure)⟩

private theorem CpRel.step {s : String} (p cp : Pos s) : CpRel phaseStep p cp :=
  ⟨fun h => absurd h (by decide : phaseStep ≠ phaseClosure),
    fun h => absurd h (by decide : phaseStep ≠ phaseStepClosure)⟩

private theorem CpRel.stepHit {s : String} {p : Pos s} (hp : p ≠ s.endPos) :
    CpRel phaseStepClosure p (p.next hp) :=
  ⟨fun h => absurd h (by decide : phaseStepClosure ≠ phaseClosure), fun _ => rem_next hp⟩

private theorem SetInv.not_mem_of_miss {den spa : WordArray} {count state si : Nat}
    (hsi : wordAt spa (4 * state) = si.toUInt32) (hsiLt : si < UInt32.size)
    (hmiss : ¬ (si < count ∧ (wordAt den (4 * si)).toNat = state)) :
    ¬ SetMem den spa count state := by
  intro hmem
  have hto : (wordAt spa (4 * state)).toNat = si := by
    rw [hsi, toNat_toUInt32_of_lt hsiLt]
  unfold SetMem at hmem
  rw [hto] at hmem
  exact hmiss hmem

private theorem RunInv.advance {s : String}
    {words : WordArray} {classes : Array ClassTable} {start : UInt32}
    {nSlots : Nat} {nStates : UInt32} {slots cRow0 nRow0 stackRow0 : USize}
    {p cp : Pos s} {cCount : UInt32} {cDen cSpa : WordArray}
    {nCount : UInt32} {nDen nSpa stkS : WordArray} {caps : ByteArray}
    {sp : Nat} {phase i : UInt32}
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i)
    (hi : (i + 1).toNat ≤ cCount.toNat) :
    RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p p cCount cDen cSpa nCount nDen nSpa stkS caps sp phaseStep (i + 1) where
  words := h.words
  start_lt := h.start_lt
  curr := h.curr
  next := h.next
  stack := h.stack
  buf := h.buf
  i_le := hi
  sp_le := h.sp_le
  phase_ok := Or.inr (Or.inr rfl)
  cp_rel := CpRel.step p p
  step_i := fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure)

private theorem RunInv.giveUp {s : String}
    {words : WordArray} {classes : Array ClassTable} {start : UInt32}
    {nSlots : Nat} {nStates : UInt32} {slots cRow0 nRow0 stackRow0 : USize}
    {p cp : Pos s} {cCount : UInt32} {cDen cSpa : WordArray}
    {nCount : UInt32} {nDen nSpa stkS : WordArray} {caps : ByteArray}
    {sp : Nat} {phase i : UInt32}
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i) :
    RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p p cCount cDen cSpa nCount nDen nSpa stkS caps sp phaseStep cCount where
  words := h.words
  start_lt := h.start_lt
  curr := h.curr
  next := h.next
  stack := h.stack
  buf := h.buf
  i_le := Nat.le_refl _
  sp_le := h.sp_le
  phase_ok := Or.inr (Or.inr rfl)
  cp_rel := CpRel.step p p
  step_i := fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure)

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
def eval {s : String}
    (words : WordArray) (classes : Array ClassTable) (start : UInt32)
    (nSlots : Nat) (nStates : UInt32) (slots : USize) (sent : UInt64)
    (cRow0 nRow0 stackRow0 : USize)
    (p cp : Pos s) (matched clos : Bool)
    (cCount : UInt32) (cDen cSpa : WordArray)
    (nCount : UInt32) (nDen nSpa : WordArray)
    (stkS : WordArray) (caps : ByteArray) (sp : Nat)
    (phase i : UInt32)
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i) : SearchRun :=
  if hstep : phase == phaseStep then
    have hphase : phase = phaseStep := (beq_iff_eq).mp hstep
    if hp : p = s.endPos then
      SearchRun.pack matched nSlots nStates cDen cSpa nDen nSpa stkS caps
    else if i == 0 && cCount == 0 && matched then
      SearchRun.pack matched nSlots nStates cDen cSpa nDen nSpa stkS caps
    else if hic : i == cCount then
      if !matched then
        have hroom : 0 < stkS.size := by
          have := h.buf.stk_ge
          omega
        have hrowLt : 2 + 2 * nStates.toNat < 2 + 2 * nStates.toNat + stkS.size := by
          have := h.buf.stk_ge
          omega
        have hw := h.buf.window stackRow0 (2 + 2 * nStates.toNat) (Or.inr h.buf.stack_row) hrowLt
        let caps := fillRow caps (rowOff stackRow0 slots) slots sent hw.1 hw.2
        let stkS := stkS.usetWord 0 start (h.stack.wordBound 0 hroom (by decide))
        have hstack : StackInv stkS 1 nStates.toNat := by
          simp only [stkS]
          exact h.stack.reset hroom start h.start_lt
        have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
          simp only [caps, stkS]
          exact (h.buf.of_size (fillRow_size _ _ _ _ hw.1 hw.2) rfl).of_size rfl (by
            rw [WordArray.usetWord_eq]
            exact (WordArray.size_uset _ _ _ _).2)
        have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
            (p.next hp) (p.next hp) cCount cDen cSpa nCount nDen nSpa stkS caps 1
            phaseClosure 0 :=
          ⟨h.words, h.start_lt, h.curr, h.next, hstack, hbuf,
            by
              rw [UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)]
              exact Nat.zero_le _,
            Nat.le_add_left 1 _, Or.inl rfl, CpRel.closure (p.next hp),
            fun hc => absurd hc (by decide : phaseClosure ≠ phaseStepClosure)⟩
        have hlt : EvalRel
            (evalMeasure (p.next hp) phaseClosure cCount 0 1 nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
          dec_rem (rem_next hp)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          (p.next hp) (p.next hp) false false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps 1
          phaseClosure 0 h'
      else
        have hz : (0 : UInt32).toNat = 0 :=
          UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)
        have h' : RunInv words classes start nSlots nStates slots nRow0 cRow0 stackRow0
            (p.next hp) (p.next hp) nCount nDen nSpa 0 cDen cSpa stkS caps 0
            phaseStep 0 :=
          ⟨h.words, h.start_lt, h.next,
            by rw [hz]; exact h.curr.clear,
            h.stack.clear,
            h.buf.swap,
            by rw [hz]; exact Nat.zero_le _,
            by rw [hz]; exact Nat.zero_le _,
            Or.inr (Or.inr rfl), CpRel.step (p.next hp) (p.next hp),
            fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure)⟩
        have hlt : EvalRel
            (evalMeasure (p.next hp) phaseStep nCount 0 0 (0 : UInt32).toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
          dec_rem (rem_next hp)
        eval words classes start nSlots nStates slots sent nRow0 cRow0 stackRow0
          (p.next hp) (p.next hp) matched false
          nCount nDen nSpa
          (0 : UInt32) cDen cSpa
          stkS caps 0
          phaseStep 0 h'
    else
      have hne : ¬ i = cCount := fun heq => hic ((beq_iff_eq).mpr heq)
      have hltI : i.toNat < cCount.toNat := Nat.lt_of_le_of_ne h.i_le (u32_toNat_ne hne)
      have hi1 : (i + 1).toNat ≤ cCount.toNat := by
        rw [toNat_u32_add_one (by
          have := hltI
          have := h.curr.count_le
          have := h.words.le_30
          omega)]
        exact Nat.succ_le_of_lt hltI
      have hlt : EvalRel
          (evalMeasure p phaseStep cCount (i + 1) sp nCount.toNat nStates.toNat)
          (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
        rw [hphase]
        exact dec_step (step_sub_succ hltI)
      have hstateB : (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ cDen.data.size := by
        rw [u32_usize i]
        exact h.curr.denBound i.toNat (Nat.lt_of_lt_of_le hltI h.curr.count_le)
      let state := cDen.ugetWord i.toUSize hstateB
      have hs : state.toNat < nStates.toNat := by
        simp only [state]
        rw [ugetWord_wordAt cDen i hstateB
          (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hltI h.curr.count_le) h.curr.n_fit)]
        exact h.curr.dense_lt i.toNat hltI
      have htagB := h.words.tagBound state hs
      have h4n : ((4 : USize)).toNat = 4 :=
        Regex.VM.Wide.toNat_uSize_ofNat_of_lt 4 (by decide)
      have h8n : ((8 : USize)).toNat = 8 :=
        Regex.VM.Wide.toNat_uSize_ofNat_of_lt 8 (by decide)
      have hoff4 := h.words.offBound state hs 4 (by rw [h4n]; decide)
      have hoff8 := h.words.offBound state hs 8 (by rw [h8n]; decide)
      have hroom : 0 < stkS.size := by
        have := h.buf.stk_ge
        omega
      have hrowLt : 2 + 2 * nStates.toNat < 2 + 2 * nStates.toNat + stkS.size := by
        have := h.buf.stk_ge
        omega
      have hdstW := h.buf.window stackRow0 (2 + 2 * nStates.toNat) (Or.inr h.buf.stack_row) hrowLt
      have haddC := h.buf.addU32 cRow0 h.buf.c_row state hs
      have hsrcW := h.buf.window (cRow0 + state.toUSize) (cRow0.toNat + state.toNat) haddC.1 haddC.2
      let base := state.toUSize * strideBytes
      let tag := words.uget base htagB
      if tag == tagDone then
        have hlt : EvalRel
            (evalMeasure p phaseStep cCount cCount sp nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
          rw [hphase]
          exact dec_step (by rw [Nat.sub_self]; exact Nat.sub_pos_of_lt hltI)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep cCount h.giveUp
      else if tag == tagChar then
        let extra := words.uget (base + 8) hoff8.1
        if (p.get hp).val == extra then
          let nextW := words.uget (base + 4) hoff4.1
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots hdstW.1 hsrcW.1 hdstW.2 hsrcW.2
          have hnextLt : nextW.toNat < nStates.toNat := by
            simp only [nextW]
            rw [h.words.word_eq state hs 4 (Or.inl h4n) hoff4.1, h4n]
            exact h.words.next_lt state.toNat hs
          let stkS := stkS.usetWord 0 nextW (h.stack.wordBound 0 hroom (by decide))
          have hstack : StackInv stkS 1 nStates.toNat := by
            simp only [stkS]
            exact h.stack.reset hroom nextW hnextLt
          have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
            simp only [caps, stkS]
            exact (h.buf.of_size (copyRow_size _ _ _ _ hdstW.1 hsrcW.1 hdstW.2 hsrcW.2) rfl).of_size
              rfl (by
                rw [WordArray.usetWord_eq]
                exact (WordArray.size_uset _ _ _ _).2)
          have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
              p (p.next hp) cCount cDen cSpa nCount nDen nSpa stkS caps 1
              phaseStepClosure i :=
            ⟨h.words, h.start_lt, h.curr, h.next, hstack, hbuf, h.i_le,
              Nat.le_add_left 1 _, Or.inr (Or.inl rfl), CpRel.stepHit hp, fun _ => hltI⟩
          have hlt : EvalRel
              (evalMeasure p phaseStepClosure cCount i 1 nCount.toNat nStates.toNat)
              (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
            unfold evalMeasure
            rw [hphase]
            unfold phaseRank
            exact lex4_4 (fuel_enter_at sp nCount.toNat nStates.toNat h.next.count_le)
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p (p.next hp) matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps 1
            phaseStepClosure i h'
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p p matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp
            phaseStep (i + 1) (h.advance hi1)
      else if hsparse : tag == tagSparse then
        let extra := words.uget (base + 8) hoff8.1
        have hcls : extra.toNat < classes.size := by
          simp only [extra]
          rw [h.words.word_eq state hs 8 (Or.inr h8n) hoff8.1, h8n]
          exact h.words.sparse_lt state.toNat hs (by
            have htag : tag = wordAt words (12 * state.toNat) := by
              simp only [tag, base]
              exact h.words.tag_eq state hs htagB
            rw [← htag]
            exact (beq_iff_eq).mp hsparse)
        let cs := classes.uget extra.toUSize (by rw [UInt32.toNat_toUSize]; exact hcls)
        if cs.contains (p.get hp) then
          let nextW := words.uget (base + 4) hoff4.1
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots hdstW.1 hsrcW.1 hdstW.2 hsrcW.2
          have hnextLt : nextW.toNat < nStates.toNat := by
            simp only [nextW]
            rw [h.words.word_eq state hs 4 (Or.inl h4n) hoff4.1, h4n]
            exact h.words.next_lt state.toNat hs
          let stkS := stkS.usetWord 0 nextW (h.stack.wordBound 0 hroom (by decide))
          have hstack : StackInv stkS 1 nStates.toNat := by
            simp only [stkS]
            exact h.stack.reset hroom nextW hnextLt
          have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
            simp only [caps, stkS]
            exact (h.buf.of_size (copyRow_size _ _ _ _ hdstW.1 hsrcW.1 hdstW.2 hsrcW.2) rfl).of_size
              rfl (by
                rw [WordArray.usetWord_eq]
                exact (WordArray.size_uset _ _ _ _).2)
          have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
              p (p.next hp) cCount cDen cSpa nCount nDen nSpa stkS caps 1
              phaseStepClosure i :=
            ⟨h.words, h.start_lt, h.curr, h.next, hstack, hbuf, h.i_le,
              Nat.le_add_left 1 _, Or.inr (Or.inl rfl), CpRel.stepHit hp, fun _ => hltI⟩
          have hlt : EvalRel
              (evalMeasure p phaseStepClosure cCount i 1 nCount.toNat nStates.toNat)
              (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
            unfold evalMeasure
            rw [hphase]
            unfold phaseRank
            exact lex4_4 (fuel_enter_at sp nCount.toNat nStates.toNat h.next.count_le)
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p (p.next hp) matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps 1
            phaseStepClosure i h'
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p p matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp
            phaseStep (i + 1) (h.advance hi1)
      else
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep (i + 1) (h.advance hi1)
  else
    have hnotStep : ¬ phase = phaseStep := fun heq => hstep ((beq_iff_eq).mpr heq)
    if hsp0 : sp == 0 then
      have hspZ : sp = 0 := (beq_iff_eq).mp hsp0
      if hfin : phase == phaseClosure || clos then
        have h0n : ((0 : USize)).toNat = 0 := USize.toNat_zero
        have h1n : ((1 : USize)).toNat = 1 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 1 (by decide)
        have hlt0 : 0 < 2 + 2 * nStates.toNat + stkS.size := by omega
        have hlt1 : 1 < 2 + 2 * nStates.toNat + stkS.size := by omega
        have hw0 := h.buf.window 0 0 (Or.inr h0n) hlt0
        have hw1 := h.buf.window 1 1 (Or.inr h1n) hlt1
        let caps :=
          if clos then
            copyRow caps (rowOff 0 slots) (rowOff 1 slots) slots hw0.1 hw1.1 hw0.2 hw1.2
          else
            caps
        have hz : (0 : UInt32).toNat = 0 :=
          UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)
        have hbuf : EvalBuf caps stkS slots nRow0 cRow0 stackRow0 nSlots nStates.toNat := by
          simp only [caps]
          split
          · exact (h.buf.swap).of_size (copyRow_size _ _ _ _ hw0.1 hw1.1 hw0.2 hw1.2) rfl
          · exact h.buf.swap
        have h' : RunInv words classes start nSlots nStates slots nRow0 cRow0 stackRow0
            cp cp nCount nDen nSpa 0 cDen cSpa stkS caps 0 phaseStep 0 :=
          ⟨h.words, h.start_lt, h.next,
            by rw [hz]; exact h.curr.clear,
            hspZ ▸ h.stack,
            hbuf,
            by rw [hz]; exact Nat.zero_le _,
            by rw [hz]; exact Nat.zero_le _,
            Or.inr (Or.inr rfl), CpRel.step cp cp,
            fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure)⟩
        have hlt : EvalRel
            (evalMeasure cp phaseStep nCount 0 0 (0 : UInt32).toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
          by_cases hph : phase = phaseClosure
          · exact dec_rank (h.cp_rel.1 hph) (by rw [hph, rank_step, rank_closure]; decide)
          · exact dec_rem (h.cp_rel.2 (phase_stepClosure_of phase h.phase_ok hnotStep hph))
        eval words classes start nSlots nStates slots sent nRow0 cRow0 stackRow0
          cp cp clos false
          nCount nDen nSpa
          (0 : UInt32) cDen cSpa
          stkS caps 0
          phaseStep 0 h'
      else
        have hnotC : ¬ phase = phaseClosure := by
          intro hph
          apply hfin
          rw [hph]
          simp [Bool.true_or]
        have hsc := phase_stepClosure_of phase h.phase_ok hnotStep hnotC
        have hltI := h.step_i hsc
        have hi1 : (i + 1).toNat ≤ cCount.toNat := by
          rw [toNat_u32_add_one (by
            have := hltI
            have := h.curr.count_le
            have := h.words.le_30
            omega)]
          exact Nat.succ_le_of_lt hltI
        have hlt : EvalRel
            (evalMeasure p phaseStep cCount (i + 1) 0 nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
          rw [hsc]
          exact dec_resume (step_sub_succ hltI)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps 0
          phaseStep (i + 1) (hspZ ▸ h.advance hi1)
    else
      have hspPos : 0 < sp := by
        have hnez : sp ≠ 0 := fun h0 => hsp0 ((beq_iff_eq).mpr h0)
        omega
      let sp' := sp - 1
      have hspLt : sp' < sp := Nat.sub_lt hspPos (by decide)
      have hsp30 : sp' < 2 ^ 30 := Nat.lt_of_lt_of_le hspLt h.stack.sp_fit
      have hstkB := h.stack.wordBound sp' (Nat.lt_of_lt_of_le hspLt h.stack.sp_le) hsp30
      let stkOff := rowOff (stackRow0 + sp'.toUSize) slots
      let state := stkS.ugetWord sp'.toUSize hstkB
      have hs : state.toNat < nStates.toNat := by
        simp only [state]
        rw [h.stack.readWord sp' hspLt]
        exact h.stack.id_lt sp' hspLt
      have hspaB : (state.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ nSpa.data.size := by
        rw [u32_usize state]
        exact h.next.spaBound state.toNat hs
      let si := nSpa.ugetWord state.toUSize hspaB
      let seen :=
        if hsi : si < nCount then
          nDen.ugetWord si.toUSize (by
            rw [u32_usize si]
            exact h.next.denBound si.toNat
              (Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hsi) h.next.count_le)) == state
        else
          false
      if hseenB : seen = true then
        have hstack : StackInv stkS sp' nStates.toNat := by
          simpa [sp'] using h.stack.pop hspPos
        have hspLe : sp' ≤ nCount.toNat + 1 := Nat.le_trans (Nat.le_of_lt hspLt) h.sp_le
        have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
            p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp' phase i :=
          ⟨h.words, h.start_lt, h.curr, h.next, hstack, h.buf, h.i_le, hspLe,
            h.phase_ok, h.cp_rel, h.step_i⟩
        have hlt : EvalRel
            (evalMeasure p phase cCount i (sp - 1) nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
          dec_fuel (fuel_pop hnotStep hspPos)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp'
          phase i h'
      else
        have hnot : ¬ SetMem nDen nSpa nCount.toNat state.toNat := by
          have hread : wordAt nSpa (4 * state.toNat) = si := by
            simp only [si]
            exact (ugetWord_wordAt nSpa state hspaB
              (Nat.lt_of_lt_of_le hs h.next.n_fit)).symm
          apply SetInv.not_mem_of_miss (si := si.toNat)
            (by rw [hread]; exact (UInt32.ofNat_toNat).symm)
            (UInt32.toNat_lt si)
          intro hbad
          have hltSi : si < nCount := (UInt32.lt_iff_toNat_lt).mpr hbad.1
          have hsiFit : si.toNat < 2 ^ 30 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hbad.1 h.next.count_le) h.next.n_fit
          have hdenB : (si.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ nDen.data.size := by
            rw [u32_usize si]
            exact h.next.denBound si.toNat (Nat.lt_of_lt_of_le hbad.1 h.next.count_le)
          have hword : nDen.ugetWord si.toUSize hdenB = state := by
            rw [ugetWord_wordAt nDen si hdenB hsiFit]
            have hEq : wordAt nDen (4 * si.toNat) = state.toNat.toUInt32 :=
              UInt32.toNat_inj.mp (by
                rw [hbad.2, toNat_toUInt32_of_lt (UInt32.toNat_lt state)])
            rw [hEq]
            exact UInt32.ofNat_toNat
          have hseen : seen = true := by
            simp only [seen]
            rw [dite_eq_left hltSi, hword]
            simp
          exact absurd hseen hseenB
        have hcountLt : nCount.toNat < nStates.toNat :=
          SetInv.lt_of_not_mem h.next state.toNat hs hnot
        have hcnt : nCount.toNat + 1 < 2 ^ 32 := by
          have := hcountLt
          have := h.words.le_30
          omega
        have htagB := h.words.tagBound state hs
        have h4n : ((4 : USize)).toNat = 4 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 4 (by decide)
        have h8n : ((8 : USize)).toNat = 8 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 8 (by decide)
        have hoff4 := h.words.offBound state hs 4 (by rw [h4n]; decide)
        have hoff8 := h.words.offBound state hs 8 (by rw [h8n]; decide)
        let base := state.toUSize * strideBytes
        let tag := words.uget base htagB
        let nextW := words.uget (base + 4) hoff4.1
        let extra := words.uget (base + 8) hoff8.1
        have h1n : ((1 : USize)).toNat = 1 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 1 (by decide)
        have hlt1 : 1 < 2 + 2 * nStates.toNat + stkS.size := by omega
        have hw1 := h.buf.window 1 1 (Or.inr h1n) hlt1
        have hslot := h.buf.stackSlot sp' (Nat.lt_of_lt_of_le hspLt h.stack.sp_le)
          (Nat.lt_trans hsp30 (by decide : 2 ^ 30 < 2 ^ 32))
        have hstkW := h.buf.window (stackRow0 + sp'.toUSize) (2 + 2 * nStates.toNat + sp')
          hslot.1 hslot.2
        have haddN := h.buf.addU32 nRow0 h.buf.n_row state hs
        have hnextW := h.buf.window (nRow0 + state.toUSize) (nRow0.toNat + state.toNat)
          haddN.1 haddN.2
        let caps1 :=
          if tag == tagDone && !clos then
            copyRow caps (rowOff 1 slots) stkOff slots hw1.1 hstkW.1 hw1.2 hstkW.2
          else
            caps
        have hsz1 : caps1.size = caps.size := by
          simp only [caps1]
          split
          · exact copyRow_size _ _ _ _ hw1.1 hstkW.1 hw1.2 hstkW.2
          · rfl
        let clos := tag == tagDone || clos
        have hnext1 :
            (rowOff (nRow0 + state.toUSize) slots).toNat + slots.toNat * 8 ≤ caps1.size := by
          rw [hsz1]
          exact hnextW.1
        have hstk1 : stkOff.toNat + slots.toNat * 8 ≤ caps1.size := by
          rw [hsz1]
          simp only [stkOff]
          exact hstkW.1
        let caps2 :=
          if writesUpdate tag then
            copyRow caps1 (rowOff (nRow0 + state.toUSize) slots) stkOff slots
              hnext1 hstk1 hnextW.2 hstkW.2
          else
            caps1
        have hsz2 : caps2.size = caps.size := by
          simp only [caps2]
          split
          · rw [copyRow_size _ _ _ _ hnext1 hstk1 hnextW.2 hstkW.2, hsz1]
          · exact hsz1
        let nDen := nDen.usetWord nCount.toUSize state (by
          rw [u32_usize nCount]
          exact h.next.denBound nCount.toNat hcountLt)
        let nSpa := nSpa.usetWord state.toUSize nCount (by
          rw [u32_usize state]
          exact h.next.spaBound state.toNat hs)
        let nCount' := nCount + 1
        have hnext : SetInv nDen nSpa nCount'.toNat nStates.toNat := by
          simp only [nDen, nSpa, nCount']
          exact SetInv.insertU32 h.next state hs hnot hcnt
        have hbuf : EvalBuf caps2 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
          simp only [caps2]
          split
          · have hbuf1 : EvalBuf caps1 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [caps1]
              split
              · exact h.buf.of_size (copyRow_size _ _ _ _ hw1.1 hstkW.1 hw1.2 hstkW.2) rfl
              · exact h.buf
            exact hbuf1.of_size (copyRow_size _ _ _ _ hnext1 hstk1 hnextW.2 hstkW.2) rfl
          · simp only [caps1]
            split
            · exact h.buf.of_size (copyRow_size _ _ _ _ hw1.1 hstkW.1 hw1.2 hstkW.2) rfl
            · exact h.buf
        have hno : ¬ sp' + 2 > stkS.size := by
          have := h.sp_le
          have := h.buf.stk_ge
          have := h.next.count_le
          omega
        have hnextLt : nextW.toNat < nStates.toNat := by
          simp only [nextW]
          rw [h.words.word_eq state hs 4 (Or.inl h4n) hoff4.1, h4n]
          exact h.words.next_lt state.toNat hs
        have hback : sp' + 1 = sp := by omega
        have hspEq : sp' = sp - 1 := by simp only [sp']
        have htop : sp' + 1 < stkS.size := by
          have := h.sp_le
          have := h.buf.stk_ge
          have := h.next.count_le
          omega
        have htop32 : sp' + 1 < 2 ^ 32 := by
          have := h.stack.sp_fit
          omega
        have hfit30 : sp + 1 ≤ 2 ^ 30 := by
          have hdiv : nStates.toNat ≤ 2 ^ 32 / 12 :=
            (Nat.le_div_iff_mul_le (by decide : 0 < 12)).mpr h.words.n_bytes
          have : 2 ^ 32 / 12 + 1 ≤ 2 ^ 30 := by decide
          have := h.sp_le
          have := hcountLt
          omega
        -- The live prefix never fills the buffer: `sp ≤ nCount + 1` and the stack
        -- was allocated with at least `n + 2` words. The check stays so the schedule
        -- is unchanged; the growing branch does not return.
        if hbad : sp' + 2 > stkS.size then
          False.elim (hno hbad)
        else
          have hwrite := h.stack.wordBound sp' (Nat.lt_of_lt_of_le hspLt h.stack.sp_le) hsp30
          have hstkSz (a : WordArray) (i : USize) (v : UInt32)
              (hb : (i * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size) :
              (a.usetWord i v hb).size = a.size := by
            rw [WordArray.usetWord_eq]
            exact (WordArray.size_uset _ _ _ _).2
          if tag == tagEpsilon then
            let stk1 := stkS.usetWord sp'.toUSize nextW hwrite
            have hstack : StackInv stk1 (sp' + 1) nStates.toNat := by
              simp only [stk1]
              exact StackInv.cast
                (h.stack.succAt hspPos nextW hnextLt sp' hspEq hwrite) rfl hback
            have hbuf1 : EvalBuf caps2 stk1 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [stk1]
              exact hbuf.of_size rfl (hstkSz _ _ _ _)
            have hspLe : sp' + 1 ≤ nCount'.toNat + 1 := by
              rw [hback, toNat_u32_add_one hcnt]
              exact Nat.le_trans h.sp_le (Nat.le_succ _)
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stk1 caps2 (sp' + 1) phase i :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf1, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i ((sp - 1) + 1) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [show (sp - 1) + 1 = sp by omega, toNat_u32_add_one hcnt]
                exact fuel_keep hnotStep hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stk1 caps2 (sp' + 1)
              phase i h'
          else if hsplit : tag == tagSplit then
            have hextraLt : extra.toNat < nStates.toNat := by
              simp only [extra]
              rw [h.words.word_eq state hs 8 (Or.inr h8n) hoff8.1, h8n]
              exact h.words.split_lt state.toNat hs (by
                have htag : tag = wordAt words (12 * state.toNat) := by
                  simp only [tag, base]
                  exact h.words.tag_eq state hs htagB
                rw [← htag]
                exact (beq_iff_eq).mp hsplit)
            have hslot2 := h.buf.stackSlot (sp' + 1) htop htop32
            have htopW := h.buf.window (stackRow0 + (sp' + 1).toUSize)
              (2 + 2 * nStates.toNat + (sp' + 1)) hslot2.1 hslot2.2
            have htopDst :
                (rowOff (stackRow0 + (sp' + 1).toUSize) slots).toNat + slots.toNat * 8 ≤
                  caps2.size := by
              rw [hsz2]
              exact htopW.1
            have htopSrc : stkOff.toNat + slots.toNat * 8 ≤ caps2.size := by
              rw [hsz2]
              simp only [stkOff]
              exact hstkW.1
            let caps3 := copyRow caps2 (rowOff (stackRow0 + (sp' + 1).toUSize) slots) stkOff slots
              htopDst htopSrc htopW.2 hstkW.2
            have hbuf3 : EvalBuf caps3 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat :=
              hbuf.of_size (copyRow_size _ _ _ _ htopDst htopSrc htopW.2 hstkW.2) rfl
            let stk1 := stkS.usetWord sp'.toUSize extra hwrite
            have hidx : (sp' + 1).toUSize = sp.toUSize := by
              apply USize.toNat_inj.mp
              rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 htop32,
                Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (by
                  have := h.stack.sp_fit
                  omega : sp < 2 ^ 32)]
              exact hback
            have hpushB :
                ((sp' + 1).toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ stk1.data.size := by
              simp only [stk1]
              rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).1, hidx]
              exact h.stack.wordBound sp (by rw [← hback]; exact htop) (Nat.lt_of_succ_le hfit30)
            let stk2 := stk1.usetWord (sp' + 1).toUSize nextW hpushB
            have hstack : StackInv stk2 (sp' + 2) nStates.toNat := by
              have hnested := h.stack.splitAt hspPos (by rw [← hback]; exact htop) hfit30
                extra nextW hextraLt hnextLt sp' hspEq hwrite hpushB hidx
              simp only [stk2, stk1]
              exact StackInv.cast hnested rfl (by omega)
            have hbuf2 : EvalBuf caps3 stk2 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [stk2, stk1]
              exact hbuf3.of_size rfl (by
                rw [hstkSz (stkS.usetWord sp'.toUSize extra hwrite) (sp' + 1).toUSize nextW hpushB,
                  hstkSz stkS sp'.toUSize extra hwrite])
            have hspLe : sp' + 2 ≤ nCount'.toNat + 1 := by
              have h2 : sp' + 2 = sp + 1 := by omega
              rw [h2, toNat_u32_add_one hcnt]
              exact Nat.add_le_add_right h.sp_le 1
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stk2 caps3 (sp' + 2) phase i :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf2, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i ((sp - 1) + 2) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [show (sp - 1) + 2 = sp + 1 by omega, toNat_u32_add_one hcnt]
                exact fuel_split hnotStep hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stk2 caps3 (sp' + 2)
              phase i h'
          else if tag == tagSave then
            let caps3 :=
              if hex : extra.toNat < nSlots then
                uset caps2 (stkOff + extra.toUSize * slotBytes) (encodePos cp) (by
                  rw [hsz2]
                  simp only [stkOff]
                  exact h.buf.slotBound (stackRow0 + sp'.toUSize)
                    (2 + 2 * nStates.toNat + sp') hslot.1 hslot.2 extra hex)
              else
                caps2
            have hbuf3 : EvalBuf caps3 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [caps3]
              split
              · exact hbuf.of_size (uset_size _ _ _ _) rfl
              · exact hbuf
            let stk1 := stkS.usetWord sp'.toUSize nextW hwrite
            have hstack : StackInv stk1 (sp' + 1) nStates.toNat := by
              simp only [stk1]
              exact StackInv.cast
                (h.stack.succAt hspPos nextW hnextLt sp' hspEq hwrite) rfl hback
            have hbuf1 : EvalBuf caps3 stk1 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [stk1]
              exact hbuf3.of_size rfl (hstkSz _ _ _ _)
            have hspLe : sp' + 1 ≤ nCount'.toNat + 1 := by
              rw [hback, toNat_u32_add_one hcnt]
              exact Nat.le_trans h.sp_le (Nat.le_succ _)
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stk1 caps3 (sp' + 1) phase i :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf1, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i ((sp - 1) + 1) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [show (sp - 1) + 1 = sp by omega, toNat_u32_add_one hcnt]
                exact fuel_keep hnotStep hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stk1 caps3 (sp' + 1)
              phase i h'
          else if tag == tagAnchor then
            if anchorTest extra cp then
              let stk1 := stkS.usetWord sp'.toUSize nextW hwrite
              have hstack : StackInv stk1 (sp' + 1) nStates.toNat := by
                simp only [stk1]
                exact StackInv.cast
                  (h.stack.succAt hspPos nextW hnextLt sp' hspEq hwrite) rfl hback
              have hbuf1 : EvalBuf caps2 stk1 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
                simp only [stk1]
                exact hbuf.of_size rfl (hstkSz _ _ _ _)
              have hspLe : sp' + 1 ≤ nCount'.toNat + 1 := by
                rw [hback, toNat_u32_add_one hcnt]
                exact Nat.le_trans h.sp_le (Nat.le_succ _)
              have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                  p cp cCount cDen cSpa nCount' nDen nSpa stk1 caps2 (sp' + 1) phase i :=
                ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf1, h.i_le, hspLe,
                  h.phase_ok, h.cp_rel, h.step_i⟩
              have hlt : EvalRel
                  (evalMeasure p phase cCount i ((sp - 1) + 1) (nCount + 1).toNat nStates.toNat)
                  (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
                dec_fuel (by
                  rw [show (sp - 1) + 1 = sp by omega, toNat_u32_add_one hcnt]
                  exact fuel_keep hnotStep hcountLt)
              eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
                p cp matched clos
                cCount cDen cSpa
                nCount' nDen nSpa
                stk1 caps2 (sp' + 1)
                phase i h'
            else
              have hstack : StackInv stkS sp' nStates.toNat := by
                simpa [sp'] using h.stack.pop hspPos
              have hspLe : sp' ≤ nCount'.toNat + 1 := by
                rw [toNat_u32_add_one hcnt]
                exact Nat.le_trans (Nat.le_of_lt hspLt) (Nat.le_trans h.sp_le (Nat.le_succ _))
              have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                  p cp cCount cDen cSpa nCount' nDen nSpa stkS caps2 sp' phase i :=
                ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf, h.i_le, hspLe,
                  h.phase_ok, h.cp_rel, h.step_i⟩
              have hlt : EvalRel
                  (evalMeasure p phase cCount i (sp - 1) (nCount + 1).toNat nStates.toNat)
                  (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
                dec_fuel (by
                  rw [toNat_u32_add_one hcnt]
                  exact fuel_discard hnotStep hspPos hcountLt)
              eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
                p cp matched clos
                cCount cDen cSpa
                nCount' nDen nSpa
                stkS caps2 sp'
                phase i h'
          else
            have hstack : StackInv stkS sp' nStates.toNat := by
              simpa [sp'] using h.stack.pop hspPos
            have hspLe : sp' ≤ nCount'.toNat + 1 := by
              rw [toNat_u32_add_one hcnt]
              exact Nat.le_trans (Nat.le_of_lt hspLt) (Nat.le_trans h.sp_le (Nat.le_succ _))
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stkS caps2 sp' phase i :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i (sp - 1) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [toNat_u32_add_one hcnt]
                exact fuel_discard hnotStep hspPos hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stkS caps2 sp'
              phase i h'
termination_by evalMeasure p phase cCount i sp nCount.toNat nStates.toNat
decreasing_by
  all_goals
    unfold EvalRel at hlt
    exact hlt

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
    let caps := fillRow caps (rowOff stackRow0 slots) slots sent lcProof lcProof
    let stkS := stkS.usetWord 0 start lcProof
    eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
      p p false false
      (0 : UInt32) cDen cSpa
      (0 : UInt32) nDen nSpa
      stkS caps 1
      phaseClosure 0
      lcProof

unsafe def captureNextBuf {s : String} (nfa : FlatNFA) (bufferSize : Nat) (p : Pos s) :
    Option (Buffer s bufferSize) :=
  let run := search nfa (Scratch.mkFor nfa.size.toNat bufferSize) (sentinelWord s) p
  if run.matched then
    some (toBuffer run.scratch.caps bufferSize lcProof lcProof)
  else
    none

/-- All non-overlapping matches, using the same empty-match advance as `Regex.Matches.next?`. -/
unsafe def findAll.go (nfa : FlatNFA) (info : OptimizationInfo) (haystack : String)
    (sent : UInt64) (pos : PosPlusOne haystack) (accum : Array Slice) (scratch : Scratch) : Array Slice :=
  if h : pos.isValid then
    let start := info.findStart (pos.asPos h)
    let run := search nfa scratch sent start
    if run.matched then
      let startPos := decode (uget run.scratch.caps 0 lcProof) lcProof
      let stopPos := decode (uget run.scratch.caps slotBytes lcProof) lcProof
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

def byteSpans (slices : Array Slice) : Array (Nat × Nat) :=
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
    ("\\b\\w+\\b", "pre café word 漢字 _x"),
    ("\\B\\w", "abcあ_"),
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
