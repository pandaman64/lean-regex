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

theorem toNat_toUInt32_of_lt {n : Nat} (h : n < UInt32.size) : n.toUInt32.toNat = n := by
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

/-- Tag word of a node. The non-matching constructors in `WordsWf.ofNFA` disagree with it. -/
def nodeTag : NFA.Node → UInt32
  | .done => tagDone
  | .fail => tagFail
  | .epsilon _ => tagEpsilon
  | .anchor _ _ => tagAnchor
  | .char _ _ => tagChar
  | .split _ _ => tagSplit
  | .save _ _ => tagSave
  | .sparse _ _ => tagSparse

theorem Encodes.tag_eq {classes : Array ClassTable} {node : NFA.Node} {tag next extra : UInt32}
    (h : Encodes classes node tag next extra) : tag = nodeTag node := by
  cases node with
  | save _ _ =>
    simp only [Encodes] at h
    exact h.2.1
  | _ =>
    simp only [Encodes] at h
    exact h.1

theorem Encodes.ne_tag {classes : Array ClassTable} {node : NFA.Node} {tag next extra t : UInt32}
    (h : Encodes classes node tag next extra) (hne : nodeTag node ≠ t) : tag ≠ t := by
  intro htag
  exact hne ((tag_eq h).symm.trans htag)

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
@[expose]
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

@[expose]
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

/--
Allocation bounds for a scratch block of `n` states and `nSlots` capture slots.

`ofNFA` already forces `n * 12 ≤ 2^32`. The stack word array and the capture
window are tighter, so the allocating entry points return `none` when this fails.
-/
abbrev layoutOk (n nSlots : Nat) : Prop :=
  0 < n ∧ n ≤ 2 ^ 30 ∧ n * 4 < 2 ^ 32 ∧
    (max (n * 4) 8) * 4 < 2 ^ 32 ∧
    (2 + 2 * n + max (n * 4) 8) * nSlots * 8 < 2 ^ 32

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

/-- A flattened well-formed NFA satisfies the bounds the hot loop reads. -/
theorem WordsWf.ofNFA {nfa : NFA} {flat : FlatNFA}
    (wf : nfa.WellFormed) (h : ofNFA nfa = some flat) :
    WordsWf flat.words flat.classes flat.size.toNat := by
  have spec := ofNFA_spec h
  have hs : nfa.size < 2 ^ 32 := by simpa [UInt32.size] using spec.2.1
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [spec.2.2.2.1]
    exact wf.size_lt
  · rw [spec.2.2.2.1]
    exact spec.2.2.1
  · rw [spec.2.2.2.1]
    exact spec.2.2.2.2.2.1
  · intro j hj
    have hjn : j < nfa.size := by rwa [spec.2.2.2.1] at hj
    exact spec.2.2.2.1.symm ▸ Encodes.next_lt wf.size_lt (ofNFA_encodes h j hjn)
      (wf.inBounds j hjn) hs
  · intro j hj hsplit
    have hjn : j < nfa.size := by rwa [spec.2.2.2.1] at hj
    have henc := ofNFA_encodes h j hjn
    have hb := wf.inBounds j hjn
    cases hn : nfa[j] with
    | split n₁ n₂ =>
      rw [hn] at henc hb
      simp only [NFA.Node.inBounds] at hb
      exact spec.2.2.2.1.symm ▸ Encodes.split_extra_lt henc hb.2 hs
    | _ =>
      rw [hn] at henc
      exact absurd hsplit (Encodes.ne_tag henc (by simp [nodeTag]; decide))
  · intro j hj hsparse
    have hjn : j < nfa.size := by rwa [spec.2.2.2.1] at hj
    have henc := ofNFA_encodes h j hjn
    cases hn : nfa[j] with
    | sparse _ _ =>
      rw [hn] at henc
      exact Encodes.sparse_idx henc
    | _ =>
      rw [hn] at henc
      exact absurd hsparse (Encodes.ne_tag henc (by simp [nodeTag]; decide))

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
@[expose]
def CpRel {s : String} (phase : UInt32) (p cp : Pos s) : Prop :=
  (phase = phaseClosure → cp = p) ∧
  (phase = phaseStepClosure → cp.remainingBytes < p.remainingBytes)


/-- Slot `j` of row `row` ends at or before the end of the `rows` window. -/
theorem rowSlot_le {nSlots rows row j : Nat}
    (hrow : row < rows) (hj : j < nSlots) :
    (row * nSlots + j) * 8 + 8 ≤ rows * nSlots * 8 := by
  have hslot : j + 1 ≤ nSlots := Nat.succ_le_of_lt hj
  have hblock : (row + 1) * nSlots ≤ rows * nSlots :=
    Nat.mul_le_mul_right nSlots (Nat.succ_le_of_lt hrow)
  have hineq : row * nSlots + (j + 1) ≤ rows * nSlots := by
    have : row * nSlots + nSlots = (row + 1) * nSlots := by rw [Nat.succ_mul]
    omega
  have hmul : (row * nSlots + j + 1) * 8 ≤ rows * nSlots * 8 :=
    Nat.mul_le_mul_right 8 hineq
  have hsplit : (row * nSlots + j + 1) * 8 = (row * nSlots + j) * 8 + 8 := by
    rw [Nat.add_mul, Nat.one_mul]
  rw [← hsplit]
  exact hmul

/-- In-bounds proof for one capture slot inside a `CapsWf` region. -/
theorem caps_slot_bound {caps : ByteArray} {nSlots rows row j : Nat}
    (hsize : rows * nSlots * 8 ≤ caps.size) (hfit : rows * nSlots * 8 ≤ 2 ^ 32)
    (hrow : row < rows) (hj : j < nSlots) :
    ((row * nSlots + j) * 8).toUSize.toNat + 8 ≤ caps.size := by
  have hle := rowSlot_le hrow hj
  have h32 : (row * nSlots + j) * 8 < 2 ^ 32 :=
    Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8)) (Nat.le_trans hle hfit)
  rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 h32]
  exact Nat.le_trans hle hsize

theorem caps_off_lt {nSlots rows row j : Nat}
    (hfit : rows * nSlots * 8 ≤ 2 ^ 32) (hrow : row < rows) (hj : j < nSlots) :
    (row * nSlots + j) * 8 < 2 ^ 32 :=
  Nat.lt_of_lt_of_le (Nat.lt_add_of_pos_right (by decide : 0 < 8))
    (Nat.le_trans (rowSlot_le hrow hj) hfit)

/-- Every aligned capture slot in the allocated rows is a real word. -/
structure CapsWf {s : String} (caps : ByteArray) (nSlots rows : Nat) : Prop where
  size_le : rows * nSlots * 8 ≤ caps.size
  fit : rows * nSlots * 8 ≤ 2 ^ 32
  word : ∀ row j, (hrow : row < rows) → (hj : j < nSlots) →
    SlotWord s (uget caps ((row * nSlots + j) * 8).toUSize (caps_slot_bound size_le fit hrow hj))

/-- Erased shape of a scratch block a search is allowed to reuse. -/
structure ScratchInv {s : String} (scratch : Scratch) : Prop where
  caps : CapsWf (s := s) scratch.caps scratch.nSlots
    (2 + 2 * scratch.nStates.toNat + scratch.stkS.size)
  curr : SetInv scratch.cDen scratch.cSpa 0 scratch.nStates.toNat
  next : SetInv scratch.nDen scratch.nSpa 0 scratch.nStates.toNat
  stack : StackInv scratch.stkS 0 scratch.nStates.toNat
  stk_ge : scratch.nStates.toNat + 2 ≤ scratch.stkS.size
  rows_size : (2 + 2 * scratch.nStates.toNat + scratch.stkS.size) * scratch.nSlots * 8 ≤
    scratch.caps.size
  rows_fit : (2 + 2 * scratch.nStates.toNat + scratch.stkS.size) * scratch.nSlots * 8 ≤ 2 ^ 32

structure SearchRun {s : String} (nSlots : Nat) (nStates : UInt32) where
  matched : Bool
  scratch : Scratch
  nSlots_eq : scratch.nSlots = nSlots
  nStates_eq : scratch.nStates = nStates
  inv : ScratchInv (s := s) scratch

def SearchRun.pack {s : String} (matched : Bool) (nSlots : Nat) (nStates : UInt32)
    (cDen cSpa nDen nSpa stkS : WordArray) (caps : ByteArray)
    (inv : ScratchInv (s := s) { cDen, cSpa, nDen, nSpa, stkS, caps, nSlots, nStates }) :
    SearchRun (s := s) nSlots nStates :=
  { matched
    scratch := { cDen, cSpa, nDen, nSpa, stkS, caps, nSlots, nStates }
    nSlots_eq := rfl
    nStates_eq := rfl
    inv }

/-- `rows * 8 ≥ 8`, so the capture window forces `nSlots` below `2^32`. -/
theorem ScratchInv.slots_lt {s : String} {scratch : Scratch}
    (h : ScratchInv (s := s) scratch) : scratch.nSlots < 2 ^ 32 := by
  let rows := 2 + 2 * scratch.nStates.toNat + scratch.stkS.size
  have hone : 1 ≤ rows := by omega
  have hle : scratch.nSlots * 8 ≤ rows * scratch.nSlots * 8 := by
    have := Nat.mul_le_mul_right (scratch.nSlots * 8) hone
    rw [Nat.one_mul, ← Nat.mul_assoc] at this
    exact this
  have h8 : scratch.nSlots * 8 ≤ 2 ^ 32 := Nat.le_trans hle h.rows_fit
  have hdiv : scratch.nSlots ≤ 2 ^ 32 / 8 :=
    (Nat.le_div_iff_mul_le (by decide : 0 < 8)).mpr h8
  exact Nat.lt_of_le_of_lt hdiv (by decide : 2 ^ 32 / 8 < 2 ^ 32)

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
    (phase i : UInt32) (sent : UInt64) : Prop where
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
  hlen : s.utf8ByteSize + 1 < 2 ^ 64
  sentOk : SlotWord s sent
  capsOk : CapsWf (s := s) caps nSlots (2 + 2 * nStates.toNat + stkS.size)

open Regex.VM.Wide (toNat_u32_add_one toNat_add_of_lt_2_pow_32 toNat_mul_of_lt_2_pow_32
  toNat_u32_mul_ofNat)

theorem u32_usize (w : UInt32) : w.toUSize = w.toNat.toUSize := by
  apply USize.toNat_inj.mp
  rw [UInt32.toNat_toUSize, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (UInt32.toNat_lt w)]

private theorem mul_stride_toNat (state : UInt32) (h : state.toNat * 12 < 2 ^ 32) :
    (state.toUSize * strideBytes).toNat = state.toNat * 12 :=
  toNat_u32_mul_ofNat state 12 (by decide) h

theorem ugetWord_wordAt (a : WordArray) (i : UInt32)
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

theorem WordsWf.tagBound {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n) :
    (state.toUSize * strideBytes).toNat + 4 ≤ words.data.size := by
  rw [h.baseNat state hs, h.data_size]
  have : state.toNat + 1 ≤ n := Nat.succ_le_of_lt hs
  omega

theorem WordsWf.offBound {words classes n} (h : WordsWf words classes n)
    (state : UInt32) (hs : state.toNat < n) (k : USize) (hk : k.toNat ≤ 8) :
    ((state.toUSize * strideBytes) + k).toNat + 4 ≤ words.data.size ∧
      ((state.toUSize * strideBytes) + k).toNat = state.toNat * 12 + k.toNat := by
  have hbase := h.baseNat state hs
  have hsum : (state.toUSize * strideBytes).toNat + k.toNat < 2 ^ 32 := by
    rw [hbase]
    exact state_byte_lt h.n_bytes hs k.toNat (by omega)
  refine ⟨?_, ?_⟩
  · rw [toNat_add_of_lt_2_pow_32 hsum, hbase, h.data_size]
    have : state.toNat + 1 ≤ n := Nat.succ_le_of_lt hs
    omega
  · rw [toNat_add_of_lt_2_pow_32 hsum, hbase]

theorem WordsWf.tag_eq {words classes n} (h : WordsWf words classes n)
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

theorem WordsWf.word_eq {words classes n} (h : WordsWf words classes n)
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
    rw [toNat_add_of_lt_2_pow_32 (by rw [hb, hk]; exact hsum), hb, hk]

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
    rw [toNat_mul_of_lt_2_pow_32 (by rw [UInt32.toNat_toUSize, h8]; exact hex8),
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
  rw [toNat_add_of_lt_2_pow_32 (by rw [hex]; exact hsum), hex, hrow]
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

/-- Byte offset of row `r`. -/
theorem rowOff_eq (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (row : USize) (r : Nat) (hidx : nSlots = 0 ∨ row.toNat = r)
    (hlt : r < 2 + 2 * n + stkS.size) :
    (rowOff row slots).toNat = r * nSlots * 8 := by
  cases Nat.eq_zero_or_pos nSlots with
  | inl h0 =>
    have hslots : slots = 0 := by
      apply USize.toNat_inj.mp
      rw [h.slots_eq, h0, USize.toNat_zero]
    rw [hslots, rowOff_slots_zero, h0]
    simp
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
    rw [rowOff_toNat row slots (by rw [hr, h.slots_eq]; exact hstrict), hr, h.slots_eq]

/-- Byte offset of slot `extra` inside row `r`. -/
theorem slotOff_eq (h : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (row : USize) (r : Nat) (hidx : nSlots = 0 ∨ row.toNat = r)
    (hlt : r < 2 + 2 * n + stkS.size) (extra : UInt32) (he : extra.toNat < nSlots) :
    ((rowOff row slots) + extra.toUSize * slotBytes).toNat =
      r * nSlots * 8 + extra.toNat * 8 := by
  have hpos : 0 < nSlots := Nat.lt_of_le_of_lt (Nat.zero_le _) he
  have hr : row.toNat = r := by
    cases hidx with
    | inl hz => exact absurd hz (Nat.ne_of_gt hpos)
    | inr hr => exact hr
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
    rw [toNat_mul_of_lt_2_pow_32 (by rw [UInt32.toNat_toUSize, h8]; exact hex8),
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
  rw [toNat_add_of_lt_2_pow_32 (by rw [hex]; exact hsum), hex, hrow]

end EvalBuf


namespace CapsWf

variable {s : String} {caps : ByteArray} {nSlots rows : Nat}

private theorem nat_slot (row j : Nat) :
    (row * nSlots + j) * 8 = row * nSlots * 8 + j * 8 := by
  rw [Nat.add_mul]

private theorem mul_row (row : Nat) : row * (nSlots * 8) = row * nSlots * 8 := by
  rw [← Nat.mul_assoc]

private theorem succ_bytes (row : Nat) :
    (row + 1) * nSlots * 8 = row * nSlots * 8 + nSlots * 8 := by
  rw [Nat.succ_mul, Nat.add_mul]

private theorem lt_of_mul8 {a b : Nat} (h : a * 8 < b * 8) : a < b := by
  cases Nat.lt_trichotomy a b with
  | inl hlt => exact hlt
  | inr hrest =>
    cases hrest with
    | inl heq =>
      subst heq
      exact absurd h (Nat.lt_irrefl _)
    | inr hgt =>
      exact absurd h (Nat.lt_asymm (Nat.mul_lt_mul_of_pos_right hgt (by decide : 0 < 8)))

private theorem mul8_succ_le {a b : Nat} (h : a * 8 < b * 8) : a * 8 + 8 ≤ b * 8 := by
  have hmul := Nat.mul_le_mul_right 8 (Nat.succ_le_of_lt (lt_of_mul8 h))
  rwa [Nat.succ_mul] at hmul

theorem zero (nSlots rows len : Nat) (hcover : rows * nSlots * 8 ≤ len)
    (hfit : rows * nSlots * 8 ≤ 2 ^ 32) (hlen : len < 2 ^ 32) :
    CapsWf (s := s) (ByteArray.zero len.toUSize) nSlots rows := by
  have hsz : (ByteArray.zero len.toUSize).size = len := by
    rw [ByteArray.zero_size, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hlen]
  refine ⟨by rw [hsz]; exact hcover, hfit, ?_⟩
  intro row j hrow hj
  rw [uget_zero]
  exact SlotWord.zero

private theorem slot_sep (dstRow srcRow : Nat) (hdst src : Nat)
    (hdstEq : hdst = dstRow * nSlots * 8) (hsrcEq : src = srcRow * nSlots * 8) :
    hdst = src ∨ hdst + nSlots * 8 ≤ src ∨ src + nSlots * 8 ≤ hdst := by
  cases Nat.lt_trichotomy dstRow srcRow with
  | inl hlt =>
    right
    left
    rw [hdstEq, hsrcEq, ← succ_bytes]
    have hmul := Nat.mul_le_mul_right (nSlots * 8) (Nat.succ_le_of_lt hlt)
    rwa [mul_row, mul_row] at hmul
  | inr hrest =>
    cases hrest with
    | inl heq =>
      left
      rw [hdstEq, hsrcEq, heq]
    | inr hgt =>
      right
      right
      rw [hdstEq, hsrcEq, ← succ_bytes]
      have hmul := Nat.mul_le_mul_right (nSlots * 8) (Nat.succ_le_of_lt hgt)
      rwa [mul_row, mul_row] at hmul

private theorem outside (row dstRow j : Nat) (_hrow : row < rows) (hj : j < nSlots)
    (hne : row ≠ dstRow) (hdst : Nat) (hdstEq : hdst = dstRow * nSlots * 8) :
    (row * nSlots + j) * 8 + 8 ≤ hdst ∨ hdst + nSlots * 8 ≤ (row * nSlots + j) * 8 := by
  have hsplit : (row * nSlots + j + 1) * 8 = (row * nSlots + j) * 8 + 8 := by
    rw [Nat.add_mul, Nat.one_mul]
  cases Nat.lt_or_gt_of_ne hne with
  | inl hlt =>
    left
    rw [hdstEq, ← hsplit, Nat.add_assoc]
    have hstep : row + 1 ≤ dstRow := Nat.succ_le_of_lt hlt
    have hj1 : j + 1 ≤ nSlots := Nat.succ_le_of_lt hj
    have hblock : (row + 1) * nSlots ≤ dstRow * nSlots :=
      Nat.mul_le_mul_right nSlots hstep
    have hineq : row * nSlots + (j + 1) ≤ (row + 1) * nSlots := by
      rw [Nat.succ_mul]
      exact Nat.add_le_add_left hj1 _
    exact Nat.mul_le_mul_right 8 (Nat.le_trans hineq hblock)
  | inr hgt =>
    right
    rw [hdstEq, ← succ_bytes]
    have hstep : dstRow + 1 ≤ row := Nat.succ_le_of_lt hgt
    have hmul := Nat.mul_le_mul_right (nSlots * 8) hstep
    rw [mul_row, mul_row] at hmul
    have hle : row * nSlots * 8 ≤ (row * nSlots + j) * 8 := by
      rw [nat_slot]
      exact Nat.le_add_right _ _
    exact Nat.le_trans hmul hle

/-- `base + j * 8` is the canonical offset of slot `j` on `row`. -/
private theorem plus_toUSize (base : USize) (row j : Nat)
    (hbase : base.toNat = row * nSlots * 8) (hrow : row < rows) (hj : j < nSlots)
    (hfit : rows * nSlots * 8 ≤ 2 ^ 32) :
    (base.toNat + j * 8).toUSize = ((row * nSlots + j) * 8).toUSize := by
  apply USize.toNat_inj.mp
  have hlt : base.toNat + j * 8 < 2 ^ 32 := by
    rw [hbase, ← nat_slot]
    exact caps_off_lt hfit hrow hj
  rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hlt,
    Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt hfit hrow hj),
    hbase, ← nat_slot]

private theorem plus_bound (hsize : rows * nSlots * 8 ≤ caps.size)
    (hfit : rows * nSlots * 8 ≤ 2 ^ 32) (base : USize) (row j : Nat)
    (hbase : base.toNat = row * nSlots * 8) (hrow : row < rows) (hj : j < nSlots) :
    ((base.toNat + j * 8).toUSize).toNat + 8 ≤ caps.size := by
  have hlt : base.toNat + j * 8 < 2 ^ 32 := by
    rw [hbase, ← nat_slot]
    exact caps_off_lt hfit hrow hj
  rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hlt, hbase, ← nat_slot]
  have hb := caps_slot_bound hsize hfit hrow hj
  rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt hfit hrow hj)] at hb
  exact hb

theorem copyRow (h : CapsWf (s := s) caps nSlots rows) (dst src slotsU : USize)
    (dstRow srcRow : Nat)
    (hdstNat : dst.toNat = dstRow * nSlots * 8) (hsrcNat : src.toNat = srcRow * nSlots * 8)
    (hslots : slotsU.toNat = nSlots) (hdstRow : dstRow < rows) (hsrcRow : srcRow < rows)
    (hDst : dst.toNat + slotsU.toNat * 8 ≤ caps.size)
    (hSrc : src.toNat + slotsU.toNat * 8 ≤ caps.size)
    (hDstFit : dst.toNat + slotsU.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + slotsU.toNat * 8 ≤ 2 ^ 32) :
    CapsWf (s := s) (FlatBuffer.copyRow caps dst src slotsU hDst hSrc hDstFit hSrcFit) nSlots rows := by
  have hsz := FlatBuffer.copyRow_size caps dst src slotsU hDst hSrc hDstFit hSrcFit
  refine ⟨by rw [hsz]; exact h.size_le, h.fit, ?_⟩
  intro row j hrow hj
  have hsep : dst.toNat = src.toNat ∨ dst.toNat + slotsU.toNat * 8 ≤ src.toNat ∨
      src.toNat + slotsU.toNat * 8 ≤ dst.toNat := by
    rw [hslots]
    exact slot_sep dstRow srcRow dst.toNat src.toNat hdstNat hsrcNat
  let caps' := FlatBuffer.copyRow caps dst src slotsU hDst hSrc hDstFit hSrcFit
  by_cases hsame : row = dstRow
  · have _ := hdstRow
    have hbase : dst.toNat = row * nSlots * 8 := by rw [hdstNat, hsame]
    have hdstOff := plus_toUSize dst row j hbase hrow hj h.fit
    have hsrcOff := plus_toUSize src srcRow j hsrcNat hsrcRow hj h.fit
    have hsrcBound := plus_bound h.size_le h.fit src srcRow j hsrcNat hsrcRow hj
    have hdstBound : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤ caps'.size := by
      rw [hsz]
      exact plus_bound h.size_le h.fit dst row j hbase hrow hj
    have hsrcAt : SlotWord s (uget caps (src.toNat + j * 8).toUSize hsrcBound) := by
      have heq := uget_congr caps ((srcRow * nSlots + j) * 8).toUSize
        (src.toNat + j * 8).toUSize hsrcOff.symm
        (caps_slot_bound h.size_le h.fit hsrcRow hj) hsrcBound
      exact heq ▸ h.word srcRow j hsrcRow hj
    have hw := FlatBuffer.copyRow_slotWord caps dst src slotsU hDst hSrc hDstFit hSrcFit hsep
      j (by rw [hslots]; exact hj) hdstBound hsrcBound hsrcAt
    have heqD := uget_congr caps' (dst.toNat + j * 8).toUSize
      ((row * nSlots + j) * 8).toUSize hdstOff hdstBound
      (caps_slot_bound (by rw [hsz]; exact h.size_le) h.fit hrow hj)
    exact heqD ▸ hw
  · have hdisj : ((row * nSlots + j) * 8).toUSize.toNat + 8 ≤ dst.toNat ∨
        dst.toNat + slotsU.toNat * 8 ≤ ((row * nSlots + j) * 8).toUSize.toNat := by
      rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt h.fit hrow hj), hslots]
      exact outside row dstRow j hrow hj hsame dst.toNat hdstNat
    exact FlatBuffer.copyRow_slotWord_disjoint caps dst src slotsU hDst hSrc hDstFit hSrcFit
      ((row * nSlots + j) * 8).toUSize (caps_slot_bound h.size_le h.fit hrow hj)
      (h.word row j hrow hj) hdisj
      (by rw [hsz]; exact caps_slot_bound h.size_le h.fit hrow hj)

theorem fillRow (h : CapsWf (s := s) caps nSlots rows) (dst slotsU : USize) (v : UInt64)
    (dstRow : Nat) (hdstNat : dst.toNat = dstRow * nSlots * 8) (hslots : slotsU.toNat = nSlots)
    (hdstRow : dstRow < rows) (hv : SlotWord s v)
    (hDst : dst.toNat + slotsU.toNat * 8 ≤ caps.size)
    (hFit : dst.toNat + slotsU.toNat * 8 ≤ 2 ^ 32) :
    CapsWf (s := s) (FlatBuffer.fillRow caps dst slotsU v hDst hFit) nSlots rows := by
  have hsz := FlatBuffer.fillRow_size caps dst slotsU v hDst hFit
  refine ⟨by rw [hsz]; exact h.size_le, h.fit, ?_⟩
  intro row j hrow hj
  let caps' := FlatBuffer.fillRow caps dst slotsU v hDst hFit
  by_cases hsame : row = dstRow
  · have _ := hdstRow
    have hbase : dst.toNat = row * nSlots * 8 := by rw [hdstNat, hsame]
    have hdstOff := plus_toUSize dst row j hbase hrow hj h.fit
    have hdstBound : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤ caps'.size := by
      rw [hsz]
      exact plus_bound h.size_le h.fit dst row j hbase hrow hj
    have hw := FlatBuffer.fillRow_slotWord caps dst slotsU v hDst hFit hv j
      (by rw [hslots]; exact hj) hdstBound
    have heqD := uget_congr caps' (dst.toNat + j * 8).toUSize
      ((row * nSlots + j) * 8).toUSize hdstOff hdstBound
      (caps_slot_bound (by rw [hsz]; exact h.size_le) h.fit hrow hj)
    exact heqD ▸ hw
  · have hdisj : ((row * nSlots + j) * 8).toUSize.toNat + 8 ≤ dst.toNat ∨
        dst.toNat + slotsU.toNat * 8 ≤ ((row * nSlots + j) * 8).toUSize.toNat := by
      rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt h.fit hrow hj), hslots]
      exact outside row dstRow j hrow hj hsame dst.toNat hdstNat
    exact FlatBuffer.fillRow_slotWord_disjoint caps dst slotsU v hDst hFit
      ((row * nSlots + j) * 8).toUSize (caps_slot_bound h.size_le h.fit hrow hj)
      (h.word row j hrow hj) hdisj
      (by rw [hsz]; exact caps_slot_bound h.size_le h.fit hrow hj)

theorem write (h : CapsWf (s := s) caps nSlots rows) (off : USize) (v : UInt64) (row j : Nat)
    (heq : off.toNat = (row * nSlots + j) * 8) (hrow : row < rows) (hj : j < nSlots)
    (hv : SlotWord s v) (hb : off.toNat + 8 ≤ caps.size) :
    CapsWf (s := s) (uset caps off v hb) nSlots rows := by
  have hsz := uset_size caps off v hb
  refine ⟨by rw [hsz]; exact h.size_le, h.fit, ?_⟩
  intro row' j' hrow' hj'
  by_cases hsame : row' = row ∧ j' = j
  · rcases hsame with ⟨hr, hjEq⟩
    have hoff : off = ((row' * nSlots + j') * 8).toUSize := by
      apply USize.toNat_inj.mp
      rw [heq, ← hr, ← hjEq,
        Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt h.fit hrow' hj')]
    have hw := uset_slotWord caps off v hb hv (by rw [hsz]; exact hb)
    have heqU := uget_congr (uset caps off v hb) off ((row' * nSlots + j') * 8).toUSize hoff
      (by rw [hsz]; exact hb) (caps_slot_bound (by rw [hsz]; exact h.size_le) h.fit hrow' hj')
    exact heqU ▸ hw
  · have hoff' : ((row' * nSlots + j') * 8).toUSize.toNat = (row' * nSlots + j') * 8 :=
      Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt h.fit hrow' hj')
    have hdisj : ((row' * nSlots + j') * 8).toUSize.toNat + 8 ≤ off.toNat ∨
        off.toNat + 8 ≤ ((row' * nSlots + j') * 8).toUSize.toNat := by
      rw [hoff', heq]
      have hne : (row' * nSlots + j') * 8 ≠ (row * nSlots + j) * 8 := by
        intro heq8
        have hdiv : row' * nSlots + j' = row * nSlots + j :=
          Nat.eq_of_mul_eq_mul_right (by decide : 0 < 8) heq8
        have hpair : row' = row ∧ j' = j := by
          cases Nat.lt_trichotomy row' row with
          | inl hlt =>
            have hltS : row' * nSlots + j' < (row' + 1) * nSlots := by
              rw [Nat.succ_mul]
              exact Nat.add_lt_add_left hj' _
            have hle := Nat.mul_le_mul_right nSlots (Nat.succ_le_of_lt hlt)
            exact absurd hdiv (Nat.ne_of_lt (Nat.lt_of_lt_of_le hltS
              (Nat.le_trans hle (Nat.le_add_right _ j))))
          | inr hrest =>
            cases hrest with
            | inl heqR =>
              subst heqR
              exact ⟨rfl, Nat.add_left_cancel hdiv⟩
            | inr hgt =>
              have hltS : row * nSlots + j < (row + 1) * nSlots := by
                rw [Nat.succ_mul]
                exact Nat.add_lt_add_left hj _
              have hle := Nat.mul_le_mul_right nSlots (Nat.succ_le_of_lt hgt)
              exact absurd hdiv.symm (Nat.ne_of_lt (Nat.lt_of_lt_of_le hltS
                (Nat.le_trans hle (Nat.le_add_right _ j'))))
        exact hsame hpair
      cases Nat.lt_or_gt_of_ne hne with
      | inl hlt =>
        left
        exact mul8_succ_le hlt
      | inr hgt =>
        right
        exact mul8_succ_le hgt
    exact uset_slotWord_disjoint caps off ((row' * nSlots + j') * 8).toUSize v hb
      (caps_slot_bound h.size_le h.fit hrow' hj') (h.word row' j' hrow' hj') hdisj
      (by rw [hsz]; exact caps_slot_bound h.size_le h.fit hrow' hj')

theorem castRows {rows' : Nat} (h : CapsWf (s := s) caps nSlots rows) (heq : rows = rows') :
    CapsWf (s := s) caps nSlots rows' := heq ▸ h

/-- Fill one row whose byte offset is `row * nSlots * 8`. -/
theorem fillAt {stkS : WordArray} {slots cRow0 nRow0 stackRow0 : USize} {n : Nat}
    (h : CapsWf (s := s) caps nSlots rows)
    (buf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (hrows : rows = 2 + 2 * n + stkS.size)
    (row : USize) (r : Nat) (hidx : nSlots = 0 ∨ row.toNat = r) (hlt : r < rows)
    (v : UInt64) (hv : SlotWord s v)
    (hDst : (rowOff row slots).toNat + slots.toNat * 8 ≤ caps.size)
    (hFit : (rowOff row slots).toNat + slots.toNat * 8 ≤ 2 ^ 32) :
    CapsWf (s := s) (FlatBuffer.fillRow caps (rowOff row slots) slots v hDst hFit) nSlots rows := by
  have hlt' : r < 2 + 2 * n + stkS.size := by rw [hrows] at hlt; exact hlt
  exact fillRow h (rowOff row slots) slots v r (buf.rowOff_eq row r hidx hlt') buf.slots_eq
    hlt hv hDst hFit

/-- Copy one row onto another. Both offsets are `row * nSlots * 8`. -/
theorem copyAt {stkS : WordArray} {slots cRow0 nRow0 stackRow0 : USize} {n : Nat}
    (h : CapsWf (s := s) caps nSlots rows)
    (buf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots n)
    (hrows : rows = 2 + 2 * n + stkS.size)
    (dst src : USize) (dstRow srcRow : Nat)
    (hdst : nSlots = 0 ∨ dst.toNat = dstRow) (hsrc : nSlots = 0 ∨ src.toNat = srcRow)
    (hdstLt : dstRow < rows) (hsrcLt : srcRow < rows)
    (hDst : (rowOff dst slots).toNat + slots.toNat * 8 ≤ caps.size)
    (hSrc : (rowOff src slots).toNat + slots.toNat * 8 ≤ caps.size)
    (hDstFit : (rowOff dst slots).toNat + slots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : (rowOff src slots).toNat + slots.toNat * 8 ≤ 2 ^ 32) :
    CapsWf (s := s) (FlatBuffer.copyRow caps (rowOff dst slots) (rowOff src slots) slots
      hDst hSrc hDstFit hSrcFit) nSlots rows := by
  have hdst' : dstRow < 2 + 2 * n + stkS.size := by rw [hrows] at hdstLt; exact hdstLt
  have hsrc' : srcRow < 2 + 2 * n + stkS.size := by rw [hrows] at hsrcLt; exact hsrcLt
  exact copyRow h (rowOff dst slots) (rowOff src slots) slots dstRow srcRow
    (buf.rowOff_eq dst dstRow hdst hdst') (buf.rowOff_eq src srcRow hsrc hsrc') buf.slots_eq
    hdstLt hsrcLt hDst hSrc hDstFit hSrcFit

/-- Write one slot addressed as `row * nSlots * 8 + j * 8`. -/
theorem writeSlot (h : CapsWf (s := s) caps nSlots rows) (off : USize) (v : UInt64)
    (row j : Nat) (heq : off.toNat = row * nSlots * 8 + j * 8)
    (hrow : row < rows) (hj : j < nSlots) (hv : SlotWord s v)
    (hb : off.toNat + 8 ≤ caps.size) :
    CapsWf (s := s) (uset caps off v hb) nSlots rows := by
  exact write h off v row j (by rw [heq, ← nat_slot]) hrow hj hv hb

private theorem slotBytes_toNat : slotBytes.toNat = 8 :=
  Regex.VM.Wide.toNat_uSize_ofNat_of_lt 8 (by decide)

/-- In-bounds proof for slot `i` of row 0, at `i * 8`. -/
theorem row0Bound (h : CapsWf (s := s) caps nSlots rows) (hrows : 0 < rows) (i : Fin nSlots) :
    (i.val.toUSize * slotBytes).toNat + 8 ≤ caps.size := by
  have hprod : i.val * 8 < 2 ^ 32 := by
    simpa [Nat.zero_mul, Nat.zero_add] using caps_off_lt h.fit hrows i.isLt
  have hi32 : i.val < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right i.val (by decide : 0 < 8)) hprod
  rw [USize.toNat_mul, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hi32, slotBytes_toNat,
    Nat.mod_eq_of_lt (Regex.VM.Wide.lt_two_pow_numBits_of_lt_2_pow_32 hprod)]
  have hb := caps_slot_bound h.size_le h.fit hrows i.isLt
  rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (caps_off_lt h.fit hrows i.isLt),
    Nat.zero_mul, Nat.zero_add] at hb
  exact hb

theorem row0Word (h : CapsWf (s := s) caps nSlots rows) (hrows : 0 < rows) (i : Fin nSlots) :
    SlotWord s (uget caps (i.val.toUSize * slotBytes) (row0Bound h hrows i)) := by
  have hword := h.word 0 i.val hrows i.isLt
  have hprod : i.val * 8 < 2 ^ 32 := by
    simpa [Nat.zero_mul, Nat.zero_add] using caps_off_lt h.fit hrows i.isLt
  have hi32 : i.val < 2 ^ 32 :=
    Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right i.val (by decide : 0 < 8)) hprod
  have hoff : i.val.toUSize * slotBytes = (i.val * 8).toUSize := by
    apply USize.toNat_inj.mp
    rw [USize.toNat_mul, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hi32, slotBytes_toNat,
      Nat.mod_eq_of_lt (Regex.VM.Wide.lt_two_pow_numBits_of_lt_2_pow_32 hprod),
      Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hprod]
  have hcanon : ((0 * nSlots + i.val) * 8).toUSize = (i.val * 8).toUSize := by
    rw [Nat.zero_mul, Nat.zero_add]
  exact (uget_congr caps ((0 * nSlots + i.val) * 8).toUSize (i.val.toUSize * slotBytes)
    (hcanon.trans hoff.symm)
    (caps_slot_bound h.size_le h.fit hrows i.isLt)
    (row0Bound h hrows i)) ▸ hword

private theorem mul_slot0 : ((0 : Nat).toUSize * slotBytes) = 0 := by
  apply USize.toNat_inj.mp
  rw [USize.toNat_mul,
    Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (by decide : 0 < 2 ^ 32),
    slotBytes_toNat, Nat.zero_mul, Nat.zero_mod, USize.toNat_zero]

private theorem mul_slot1 : ((1 : Nat).toUSize * slotBytes) = slotBytes := by
  apply USize.toNat_inj.mp
  rw [USize.toNat_mul, Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (by decide : 1 < 2 ^ 32),
    slotBytes_toNat, Nat.one_mul,
    Nat.mod_eq_of_lt (Regex.VM.Wide.lt_two_pow_numBits_of_lt_2_pow_32 (by decide : 8 < 2 ^ 32))]

/-- Slot 0 of row 0 sits at byte offset 0. -/
theorem slot0Bound (h : CapsWf (s := s) caps nSlots rows) (hrows : 0 < rows) (hz : 0 < nSlots) :
    (0 : USize).toNat + 8 ≤ caps.size := by
  have hb := row0Bound h hrows ⟨0, hz⟩
  rwa [mul_slot0] at hb

theorem slot0Word (h : CapsWf (s := s) caps nSlots rows) (hrows : 0 < rows) (hz : 0 < nSlots)
    (hb : (0 : USize).toNat + 8 ≤ caps.size) :
    SlotWord s (uget caps 0 hb) := by
  have hword := row0Word h hrows ⟨0, hz⟩
  exact (uget_congr caps ((0 : Nat).toUSize * slotBytes) 0 mul_slot0
    (row0Bound h hrows ⟨0, hz⟩) hb) ▸ hword

/-- Slot 1 of row 0 sits at byte offset `slotBytes`. -/
theorem slot1Bound (h : CapsWf (s := s) caps nSlots rows) (hrows : 0 < rows) (h1 : 1 < nSlots) :
    slotBytes.toNat + 8 ≤ caps.size := by
  have hb := row0Bound h hrows ⟨1, h1⟩
  rwa [mul_slot1] at hb

theorem slot1Word (h : CapsWf (s := s) caps nSlots rows) (hrows : 0 < rows) (h1 : 1 < nSlots)
    (hb : slotBytes.toNat + 8 ≤ caps.size) :
    SlotWord s (uget caps slotBytes hb) := by
  have hword := row0Word h hrows ⟨1, h1⟩
  exact (uget_congr caps ((1 : Nat).toUSize * slotBytes) slotBytes mul_slot1
    (row0Bound h hrows ⟨1, h1⟩) hb) ▸ hword

end CapsWf

private theorem cap_ge (n : Nat) (hpos : 0 < n) : n + 2 ≤ max (n * 4) 8 := by
  cases Nat.le_total (n * 4) 8 with
  | inl hle =>
    rw [Nat.max_eq_right hle]
    have hn : n ≤ 2 :=
      Nat.le_of_mul_le_mul_right
        (by
          have h8 : (2 : Nat) * 4 = 8 := by decide
          simpa [h8] using hle)
        (by decide : 0 < 4)
    omega
  | inr hge =>
    rw [Nat.max_eq_left hge]
    have hn : 2 ≤ n := by
      cases n with
      | zero => omega
      | succ k =>
        cases k with
        | zero =>
          simp at hge
        | succ m =>
          exact Nat.le_add_left 2 m
    have hsum : n + 2 ≤ n + n := Nat.add_le_add_left hn n
    rw [← Nat.two_mul] at hsum
    have hmul : 2 * n ≤ 4 * n := Nat.mul_le_mul_right n (by decide : 2 ≤ 4)
    rw [Nat.mul_comm 4 n] at hmul
    exact Nat.le_trans hsum (Nat.le_trans hmul (Nat.le_refl _))

/-- A block from `Scratch.mkFor` is a legal search scratch when `layoutOk` holds. -/
theorem ScratchInv.ofMkFor {s : String} (n nSlots : Nat) (hl : layoutOk n nSlots) :
    ScratchInv (s := s) (Scratch.mkFor n nSlots) := by
  have hpos : 0 < n := hl.1
  have h30 : n ≤ 2 ^ 30 := hl.2.1
  have h4 : n * 4 < 2 ^ 32 := hl.2.2.1
  have hcap4 : (max (n * 4) 8) * 4 < 2 ^ 32 := hl.2.2.2.1
  have hwin : (2 + 2 * n + max (n * 4) 8) * nSlots * 8 < 2 ^ 32 := hl.2.2.2.2
  have hn32 : n < UInt32.size := by
    simpa [UInt32.size] using Nat.lt_of_le_of_lt h30 (by decide : 2 ^ 30 < 2 ^ 32)
  have hnat : n.toUInt32.toNat = n := toNat_toUInt32_of_lt hn32
  have hge : n + 2 ≤ max (n * 4) 8 := cap_ge n hpos
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [Scratch.mkFor]
    have hrows : 2 + 2 * n.toUInt32.toNat + (WordArray.zeros (max (n * 4) 8)).size =
        2 + 2 * n + max (n * 4) 8 := by
      rw [hnat, (WordArray.zeros_spec (max (n * 4) 8) hcap4).1]
    rw [hrows]
    exact CapsWf.zero nSlots (2 + 2 * n + max (n * 4) 8)
      ((2 + 2 * n + max (n * 4) 8) * nSlots * 8)
      (Nat.le_refl _) (Nat.le_of_lt hwin) hwin
  · simp only [Scratch.mkFor]
    rw [hnat]
    exact SetInv.ofZeros n h4 h30
  · simp only [Scratch.mkFor]
    rw [hnat]
    exact SetInv.ofZeros n h4 h30
  · simp only [Scratch.mkFor]
    rw [hnat]
    exact StackInv.empty (WordArray.zeros (max (n * 4) 8)) n
      (WordArray.zeros_spec (max (n * 4) 8) hcap4).2
  · simp only [Scratch.mkFor]
    rw [hnat, (WordArray.zeros_spec (max (n * 4) 8) hcap4).1]
    exact hge
  · simp only [Scratch.mkFor]
    rw [hnat, (WordArray.zeros_spec (max (n * 4) 8) hcap4).1, ByteArray.zero_size,
      Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 hwin]
    exact Nat.le_refl _
  · simp only [Scratch.mkFor]
    rw [hnat, (WordArray.zeros_spec (max (n * 4) 8) hcap4).1]
    exact Nat.le_of_lt hwin

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

end Regex.VM.Refined

end
