namespace Char

def isWordChar (ch : Char) : Bool :=
  ch.isAlphanum || ch = '_'

end Char

-- These theorems are backported from https://github.com/leanprover/lean4/pull/11289
namespace String

theorem Slice.Pos.le_of_not_lt {s : Slice} {p q : s.Pos} : ¬q < p → p ≤ q := by
  simp [Slice.Pos.le_iff, Slice.Pos.lt_iff, Pos.Raw.le_iff, Pos.Raw.lt_iff]

theorem Slice.Pos.ne_endPos_of_lt {s : Slice} {p q : s.Pos} : p < q → p ≠ s.endPos := by
  have := q.isValidForSlice.le_utf8ByteSize
  simp [lt_iff, Pos.ext_iff, Pos.Raw.lt_iff, Pos.Raw.ext_iff]
  omega

theorem Slice.Pos.next_le_of_lt {s : Slice} {p q : s.Pos} {h} : p < q → p.next h ≤ q := by
  -- Things like this will become a lot simpler once we have the `Splits` machinery developed,
  -- but this is `String.Basic`, so we have to suffer a little.
  refine fun hpq => le_of_not_lt (fun hq => ?_)
  have := q.isUTF8FirstByte_byte (h := ne_endPos_of_lt hq)
  rw [byte, getUTF8Byte, String.getUTF8Byte] at this
  simp only [Pos.Raw.byteIdx_offsetBy] at this
  have h₁ : q.offset.byteIdx = p.offset.byteIdx + (q.offset.byteIdx - p.offset.byteIdx) := by
    simp [lt_iff, Pos.Raw.lt_iff] at hpq
    omega
  have h₂ : q.offset.byteIdx - p.offset.byteIdx < (p.get h).utf8Size := by
    simp [lt_iff, Pos.Raw.lt_iff] at hq
    omega
  conv at this => congr; arg 2; rw [h₁, ← Nat.add_assoc]
  rw [← ByteArray.getElem_extract (start := s.startInclusive.offset.byteIdx + p.offset.byteIdx)
    (stop := s.startInclusive.offset.byteIdx + p.offset.byteIdx + (p.get h).utf8Size)] at this
  · simp only [← utf8Encode_get_eq_extract, List.utf8Encode_singleton] at this
    have h₃ := List.getElem_toByteArray (l := utf8EncodeChar (p.get h))
      (i := q.offset.byteIdx - p.offset.byteIdx) (h := by simpa)
    rw [h₃, UInt8.isUTF8FirstByte_getElem_utf8EncodeChar] at this
    simp only [lt_iff, Pos.Raw.lt_iff] at hpq
    omega
  · simp only [ByteArray.size_extract, size_bytes]
    rw [Nat.min_eq_left]
    · omega
    · have := (p.next h).str.isValid.le_utf8ByteSize
      simpa [Nat.add_assoc] using this

theorem Slice.Pos.ofSlice_le_iff {s : String} {p : s.toSlice.Pos} {q : s.ValidPos} :
    p.ofSlice ≤ q ↔ p ≤ q.toSlice := Iff.rfl

@[simp]
theorem ValidPos.toSlice_lt_toSlice_iff {s : String} {p q : s.ValidPos} :
    p.toSlice < q.toSlice ↔ p < q := Iff.rfl

theorem ValidPos.next_le_of_lt {s : String} {p q : s.ValidPos} {h} : p < q → p.next h ≤ q := by
  rw [next, Slice.Pos.ofSlice_le_iff, ← ValidPos.toSlice_lt_toSlice_iff]
  exact Slice.Pos.next_le_of_lt

end String

namespace String.ValidPos

open Char

variable {s : String}

def isCurrWord (p : ValidPos s) : Bool :=
  if h : p ≠ s.endValidPos then
    isWordChar (p.get h)
  else
    false

def isPrevWord (p : ValidPos s) : Bool :=
  if h : p ≠ s.startValidPos then
    isWordChar ((p.prev h).get (by simp))
  else
    false

def isAtWordBoundary (p : ValidPos s) : Bool :=
  isCurrWord p != isPrevWord p

def isAtNonWordBoundary (p : ValidPos s) : Bool :=
  isCurrWord p == isPrevWord p

@[specialize]
def find (pos : ValidPos s) (p : Char → Bool) :=
  if hn : pos = s.endValidPos then
    pos
  else if p (pos.get hn) then
    pos
  else
    find (pos.next hn) p
termination_by pos

end String.ValidPos

namespace String.ValidPos

theorem ne_endValidPos_of_lt {s : String} {pos pos' : ValidPos s} (lt : pos < pos') : pos ≠ s.endValidPos := by
  intro eq
  have : pos'.offset ≤ s.endValidPos.offset := pos'.isValid.le_rawEndPos
  exact Nat.not_le_of_lt (eq ▸ lt) this

@[grind ., simp]
theorem ne_next {s : String} {pos : ValidPos s} {ne : pos ≠ s.endValidPos} : pos ≠ pos.next ne := by
  intro eq
  have : pos.next ne < pos.next ne := eq ▸ pos.lt_next
  exact (Nat.lt_irrefl _ this).elim

def posRevInduction.{u} {s : String} {motive : ValidPos s → Sort u}
  (endValidPos : motive s.endValidPos)
  (next : ∀ p : ValidPos s, (h : p ≠ s.endValidPos) → motive (p.next h) → motive p)
  (p : ValidPos s) : motive p :=
  if h : p = s.endValidPos then
    h ▸ endValidPos
  else
    next p h (posRevInduction endValidPos next (p.next h))
  termination_by p

theorem splits_of_next {s l r : String} {p : ValidPos s} {h : p ≠ s.endValidPos}
  (sp : (p.next h).Splits (l ++ singleton (p.get h)) r) : p.Splits l (singleton (p.get h) ++ r) where
  eq_append := by simp only [sp.eq_append, String.append_assoc]
  offset_eq_rawEndPos := by simpa [offset_next, Pos.Raw.ext_iff] using sp.offset_eq_rawEndPos

theorem splits_get_singleton {s l r : String} {c : Char} {p : ValidPos s} (sp : p.Splits l (singleton c ++ r)) :
  p.get sp.ne_endValidPos_of_singleton = c := by
  obtain ⟨r', h⟩ := sp.exists_eq_singleton_append sp.ne_endValidPos_of_singleton
  simp only [singleton_append_inj] at h
  exact h.1.symm

theorem lt_or_eq_of_le {s : String} {p p' : ValidPos s} (le : p ≤ p') : p < p' ∨ p = p' := by
  cases Nat.lt_or_eq_of_le le with
  | inl lt => exact .inl lt
  | inr eq => exact .inr (by simp [ValidPos.ext_iff, Pos.Raw.ext_iff, eq])

theorem Splits.exists_eq_append_left_of_lt {s l r : String} {p p' : ValidPos s} (sp : p.Splits l r) (lt : p' < p) :
  ∃ l₁ l₂, l = l₁ ++ l₂ ∧ p'.Splits l₁ (l₂ ++ r) := by
  induction p' using posRevInduction with
  | endValidPos => exact (Nat.not_lt_of_le p.isValid.le_rawEndPos lt).elim
  | next p' h ih =>
    have : p'.next h < p ∨ p'.next h = p := lt_or_eq_of_le (next_le_of_lt lt)
    cases this with
    | inl lt' =>
      obtain ⟨l₁, l₂, rfl, sp'⟩ := ih lt'
      obtain ⟨l₁, rfl⟩ := sp'.exists_eq_append_singleton
      refine ⟨l₁, singleton (p'.get h) ++ l₂, by rw [String.append_assoc], ?_⟩
      simpa only [String.append_assoc] using splits_of_next sp'
    | inr eq =>
      subst eq
      obtain ⟨l, rfl⟩ := sp.exists_eq_append_singleton
      exact ⟨l, singleton (p'.get h), rfl, splits_of_next sp⟩

theorem next_inj {s} {pos pos' : ValidPos s} {h : pos ≠ s.endValidPos} {h' : pos' ≠ s.endValidPos}
  (eq : pos.next h = pos'.next h') :
  pos = pos' := by
  have eq' := (pos.splits_next h).eq_left (eq ▸ pos'.splits_next h')
  simp only [append_singleton, push_inj] at eq'
  exact ValidPos.ext (Eq.trans (eq'.1 ▸ pos.splits.offset_eq_rawEndPos) (pos'.splits.offset_eq_rawEndPos).symm)

theorem lt_of_le_of_ne {s} {pos pos' : ValidPos s} (le : pos ≤ pos') (ne : pos ≠ pos') : pos < pos' :=
  Nat.lt_of_le_of_ne le (by simpa [ValidPos.ext_iff, Pos.Raw.ext_iff] using ne)

theorem le_of_lt_next {s} {pos pos' : ValidPos s} {h' : pos' ≠ s.endValidPos} (lt : pos < pos'.next h') : pos ≤ pos' :=
  Decidable.by_contra (fun nle => Nat.not_lt_of_le (ValidPos.next_le_of_lt (Nat.lt_of_not_le nle)) lt)

theorem le_or_eq_of_le_next {s} {pos pos' : ValidPos s} {h' : pos' ≠ s.endValidPos} (le : pos ≤ pos'.next h') :
  pos ≤ pos' ∨ pos = pos'.next h' :=
  Decidable.byCases
    (fun (eq : pos = pos'.next h') => .inr eq)
    (fun (ne : pos ≠ pos'.next h') => .inl (le_of_lt_next (lt_of_le_of_ne le ne)))

theorem le_next_iff {s} {pos pos' : ValidPos s} {h' : pos' ≠ s.endValidPos} :
  pos ≤ pos'.next h' ↔ pos ≤ pos' ∨ pos = pos'.next h' := by
  refine ⟨le_or_eq_of_le_next, ?_⟩
  intro h
  cases h with
  | inl le => exact le_trans le (le_of_lt pos'.lt_next)
  | inr eq => exact eq ▸ le_refl _

theorem lt_next_iff {s} {pos pos' : ValidPos s} {h' : pos' ≠ s.endValidPos} : pos < pos'.next h' ↔ pos ≤ pos' :=
  ⟨le_of_lt_next, fun le => Nat.lt_of_le_of_lt le pos'.lt_next⟩

theorem le_iff_lt_or_eq {s} {pos pos' : ValidPos s} : pos ≤ pos' ↔ pos < pos' ∨ pos = pos' :=
  Iff.trans Nat.le_iff_lt_or_eq (or_congr Iff.rfl (by simp [ValidPos.ext_iff, Pos.Raw.ext_iff]))

theorem lt_next_iff_lt_or_eq {s} {pos pos' : ValidPos s} (h' : pos' ≠ s.endValidPos) :
  pos < pos'.next h' ↔ pos < pos' ∨ pos = pos' :=
  lt_next_iff.trans le_iff_lt_or_eq

end String.ValidPos

namespace String

@[ext]
structure ValidPosPlusOne (s : String) where
  offset : Pos.Raw
  isValidOrPlusOne : offset.IsValid s ∨ offset = s.rawEndPos.offsetBy ⟨1⟩
deriving Repr, DecidableEq

namespace ValidPosPlusOne

variable {s : String}

-- Doesn't seem to work at the moment
@[match_pattern]
def validPos (p : ValidPos s) : ValidPosPlusOne s :=
  ⟨p.offset, .inl p.isValid⟩

@[match_pattern]
def sentinel (s : String) : ValidPosPlusOne s :=
  ⟨s.rawEndPos.offsetBy ⟨1⟩, .inr rfl⟩

@[elab_as_elim]
def rec'.{u} {motive : ValidPosPlusOne s → Sort u}
  (validPos : (p : ValidPos s) → motive (validPos p))
  (sentinel : motive (sentinel s))
  (p : ValidPosPlusOne s) : motive p :=
  if h : p.offset = s.rawEndPos.offsetBy ⟨1⟩ then
    have eq : p = .sentinel s := by
      simp [ValidPosPlusOne.ext_iff, h, ValidPosPlusOne.sentinel]
    eq ▸ sentinel
  else
    have h' : p.offset.IsValid s := by
      cases p.isValidOrPlusOne with
      | inl h => exact h
      | inr h => contradiction
    validPos ⟨p.offset, h'⟩

instance : Inhabited (ValidPosPlusOne s) := ⟨.validPos s.startValidPos⟩

def isValid (p : ValidPosPlusOne s) : Bool :=
  p.offset.isValid s

def asValidPos (p : ValidPosPlusOne s) (h : p.isValid) : ValidPos s :=
  ⟨p.offset, Pos.Raw.isValid_eq_true_iff.mp h⟩

def lt (p₁ p₂ : ValidPosPlusOne s) : Prop :=
  p₁.offset < p₂.offset

instance : LT (ValidPosPlusOne s) := ⟨lt⟩

theorem lt_iff {p₁ p₂ : ValidPosPlusOne s} : p₁ < p₂ ↔ p₁.offset < p₂.offset :=
  Iff.rfl

instance {s : String} (p₁ p₂ : ValidPosPlusOne s) : Decidable (p₁ < p₂) :=
  decidable_of_iff' _ lt_iff

def next (p : ValidPosPlusOne s) (h : p.isValid) : ValidPosPlusOne s :=
  let vp := p.asValidPos h
  if h' : vp ≠ s.endValidPos then
    .validPos (vp.next h')
  else
    .sentinel s

theorem lt_sentinel_of_valid {p : ValidPosPlusOne s} (h : p.isValid) : p < .sentinel s :=
  Nat.lt_of_le_of_lt (p.asValidPos h).isValid.le_rawEndPos (by simp [sentinel])

@[simp, grind →]
theorem lt_next (p : ValidPosPlusOne s) (h : p.isValid) : p < p.next h := by
  fun_cases next
  next vp ne => exact ValidPos.lt_next (p.asValidPos h) (h := ne)
  next => exact lt_sentinel_of_valid h

def remainingBytes (p : ValidPosPlusOne s) : Nat :=
  s.rawEndPos.byteIdx + 1 - p.offset.byteIdx

theorem lt_iff_remainingBytes_lt {p₁ p₂ : ValidPosPlusOne s} : p₁ < p₂ ↔ p₂.remainingBytes < p₁.remainingBytes := by
  simp only [lt_iff, Pos.Raw.lt_iff, remainingBytes, byteIdx_rawEndPos]
  have : p₂.offset.byteIdx ≤ s.utf8ByteSize + 1 := by
    cases p₂.isValidOrPlusOne with
    | inl h => exact Nat.le_trans h.le_utf8ByteSize (by grind)
    | inr h => simp [h, Nat.add_comm]
  grind

theorem wellFounded_gt : WellFounded (fun (p : ValidPosPlusOne s) q => q < p) := by
  simpa [lt_iff_remainingBytes_lt] using InvImage.wf remainingBytes Nat.lt_wfRel.wf

instance : WellFoundedRelation (ValidPosPlusOne s) where
  rel p q := q < p
  wf := wellFounded_gt

end ValidPosPlusOne

def startValidPosPlusOne (s : String) : ValidPosPlusOne s :=
  .validPos s.startValidPos

end String
