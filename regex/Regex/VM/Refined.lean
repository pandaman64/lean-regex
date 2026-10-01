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
        let caps := fillRow caps (rowOff stackRow0 slots) slots sent lcProof lcProof
        let stkS := stkS.usetWord 0 start lcProof
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
      let state := cDen.ugetWord i.toUSize lcProof
      let base := state.toUSize * strideBytes
      let tag := words.uget base lcProof
      if tag == tagDone then
        -- Lower-priority threads lose to the `.done` state already in this set.
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep cCount
      else if tag == tagChar then
        let extra := words.uget (base + 8) lcProof
        if (p.get hp).val == extra then
          let nextW := words.uget (base + 4) lcProof
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots lcProof lcProof lcProof lcProof
          let stkS := stkS.usetWord 0 nextW lcProof
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
        let extra := words.uget (base + 8) lcProof
        let cs := classes.uget extra.toUSize lcProof
        if cs.contains (p.get hp) then
          let nextW := words.uget (base + 4) lcProof
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots lcProof lcProof lcProof lcProof
          let stkS := stkS.usetWord 0 nextW lcProof
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
        if clos then copyRow caps (rowOff 0 slots) (rowOff 1 slots) slots lcProof lcProof lcProof lcProof else caps
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
    let state := stkS.ugetWord sp'.toUSize lcProof
    let si := nSpa.ugetWord state.toUSize lcProof
    let seen := if si < nCount then nDen.ugetWord si.toUSize lcProof == state else false
    if seen then
      eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
        p cp matched clos
        cCount cDen cSpa
        nCount nDen nSpa
        stkS caps sp'
        phase i
    else
      let base := state.toUSize * strideBytes
      let tag := words.uget base lcProof
      let nextW := words.uget (base + 4) lcProof
      let extra := words.uget (base + 8) lcProof
      -- First `.done` wins. Copy into row 1 before any later save mutates this stack row.
      let caps :=
        if tag == tagDone && !clos then
          copyRow caps (rowOff 1 slots) stkOff slots lcProof lcProof lcProof lcProof
        else
          caps
      let clos := tag == tagDone || clos
      let caps :=
        if writesUpdate tag then
          copyRow caps (rowOff (nRow0 + state.toUSize) slots) stkOff slots lcProof lcProof lcProof lcProof
        else
          caps
      let nDen := nDen.usetWord nCount.toUSize state lcProof
      let nSpa := nSpa.usetWord state.toUSize nCount lcProof
      let nCount := nCount + 1
      -- Two free slots cover a `.split` (next₂ under next₁, so next₁ is popped first).
      let grew := sp' + 2 > stkS.size
      let caps := if grew then growRows caps 2 nSlots else caps
      let stkS := if grew then stkS.push 0 |>.push 0 else stkS
      if tag == tagEpsilon then
        let stkS := stkS.usetWord sp'.toUSize nextW lcProof
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps (sp' + 1)
          phase i
      else if tag == tagSplit then
        -- The two branches must not share one mutable row.
        let caps := copyRow caps (rowOff (stackRow0 + (sp' + 1).toUSize) slots) stkOff slots
          lcProof lcProof lcProof lcProof
        let stkS := stkS.usetWord sp'.toUSize extra lcProof
        let stkS := stkS.usetWord (sp' + 1).toUSize nextW lcProof
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
            uset caps (stkOff + extra.toUSize * slotBytes) (encodePos cp) lcProof
          else
            caps
        let stkS := stkS.usetWord sp'.toUSize nextW lcProof
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps (sp' + 1)
          phase i
      else if tag == tagAnchor then
        if anchorTest extra cp then
          let stkS := stkS.usetWord sp'.toUSize nextW lcProof
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
    let caps := fillRow caps (rowOff stackRow0 slots) slots sent lcProof lcProof
    let stkS := stkS.usetWord 0 start lcProof
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
