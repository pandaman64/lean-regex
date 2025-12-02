-- namespace String

-- theorem _root_.List.asString_cons {c : Char} {cs : List Char} :
--   (c :: cs).asString = [c].asString ++ cs.asString := by
--   simp [←List.asString_append]

-- theorem Pos.Raw.utf8GetAux_utf8Size_le_utf8Encode_size (cs₁ cs₂ cs₃ : List Char) (i p : Pos.Raw)
--   (eq₁ : i = cs₁.asString.endPos) (eq₂ : p = (cs₁ ++ cs₂).asString.endPos) (lt : 0 < cs₃.length) (v : p.IsValid (cs₁ ++ cs₂ ++ cs₃).asString) :
--   (Pos.Raw.utf8GetAux (cs₂ ++ cs₃) i p).utf8Size ≤ cs₃.asString.utf8ByteSize := by
--   match cs₂, cs₃, lt with
--   | [], c :: cs₃, _ =>
--     simp only [List.append_nil] at eq₂
--     simp only [← eq₂] at eq₁
--     simp only [List.nil_append, eq₁, utf8GetAux, ↓reduceIte, ge_iff_le]
--     rw [List.asString_cons, String.utf8ByteSize_append, ←String.singleton_eq, String.utf8ByteSize_singleton]
--     exact Nat.le_add_right _ _
--   | c :: cs₂, cs₃, lt =>
--     have ne : i ≠ p := by
--       refine Pos.Raw.ne_of_lt ?_
--       simp only [eq₁, endPos, eq₂, List.asString_append, utf8ByteSize_append, mk_lt_mk, Nat.lt_add_right_iff_pos]
--       rw [List.asString_cons, String.utf8ByteSize_append, ←String.singleton_eq, String.utf8ByteSize_singleton]
--       exact Nat.lt_of_lt_of_le c.utf8Size_pos (by grind)
--     simp only [List.cons_append, utf8GetAux, ne, ↓reduceIte, ge_iff_le]
--     exact utf8GetAux_utf8Size_le_utf8Encode_size (cs₁ ++ [c]) cs₂ cs₃ (i + c) p (by simp [eq₁, endPos, ←String.singleton_eq, Pos.Raw.ext_iff]) (by simpa using eq₂) lt (by simpa using v)

-- theorem Pos.Raw.next_le_endPos {s : String} {p : Pos.Raw} (v : p.IsValid s) (h : p ≠ s.endPos) : p.next s ≤ s.endPos := by
--   have ⟨m₁, m₂, eq₁, eq₂⟩ := Pos.Raw.isValid_iff_exists_append.mp v
--   have lt : 0 < m₂.length := by
--     apply Nat.zero_lt_of_ne_zero
--     intro eq
--     have eq' : m₂ = "" := String.data_eq_nil_iff.mp (List.eq_nil_iff_length_eq_zero.mpr (by simpa using eq))
--     simp_all
--   have le := Pos.Raw.utf8GetAux_utf8Size_le_utf8Encode_size [] m₁.data m₂.data 0 p rfl (by simpa using eq₂) lt (by simpa [←eq₁] using v)
--   have eq : (utf8GetAux (m₁.data ++ m₂.data) 0 p) = p.get s := by
--     congr
--     simp [eq₁]
--   rw [eq] at le
--   simp only [next, le_iff, byteIdx_add_char, byteIdx_endPos, ge_iff_le]
--   calc p.byteIdx + (get s p).utf8Size
--     _ ≤ p.byteIdx + m₂.data.asString.utf8ByteSize := by grind
--     _ ≤ m₁.endPos.byteIdx + m₂.data.asString.utf8ByteSize := by grind
--     _ ≤ s.utf8ByteSize := by simp [eq₁]

-- theorem Pos.Raw.utf8GetAux_eq_default_of_not_valid (cs₁ cs₂ : List Char) (i p : Pos.Raw)
--   (eq : i = cs₁.asString.endPos)
--   (h : i.IsValid (cs₁ ++ cs₂).asString) (h' : ¬p.IsValid (cs₁ ++ cs₂).asString) :
--   Pos.Raw.utf8GetAux cs₂ i p = default := by
--   fun_induction Pos.Raw.utf8GetAux generalizing cs₁
--   next => rfl
--   next => grind
--   next c cs₂ i p ne ih =>
--     have eq' : i + c = (cs₁ ++ [c]).asString.endPos := by
--       simp [eq, String.endPos, Pos.Raw.ext_iff, ←String.singleton_eq_asString]
--     have h : IsValid (cs₁ ++ [c] ++ cs₂).asString (i + c) := by
--       rw [Pos.Raw.isValid_iff_exists_append]
--       exists (cs₁ ++ [c]).asString, cs₂.asString
--       refine ⟨List.asString_append, ?_⟩
--       simp [eq, ←String.singleton_eq_asString, String.endPos, Pos.Raw.ext_iff]
--     exact ih (cs₁ ++ [c]) eq' h (by simpa using h')

-- theorem Pos.Raw.get_eq_default_of_not_valid {p : Pos.Raw} {s : String} (h : ¬p.IsValid s) : p.get s = default :=
--   Pos.Raw.utf8GetAux_eq_default_of_not_valid [] s.data 0 p rfl Pos.Raw.isValid_zero (by simpa using h)

-- theorem next_le_endPos (s : String) (p : Pos.Raw) (lt : p < s.endPos) : p.next s ≤ s.endPos := by
--   if v : p.IsValid s then
--     exact Pos.Raw.next_le_endPos v (ne_of_apply_ne Pos.Raw.byteIdx (Nat.ne_of_lt lt))
--   else
--     simpa [Pos.Raw.next, Pos.Raw.get_eq_default_of_not_valid v] using Nat.succ_le_of_lt lt

-- end String

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

-- theorem next'_eq_next (it : Iterator) (h : it.hasNext) : it.next' h = it.next := by
--   simp [next', next]

-- theorem next_toString (it : Iterator) : it.next.toString = it.toString := by
--   simp [next, toString]

-- theorem next_le_endPos (it : Iterator) (h : it.hasNext) : (it.next' h).pos ≤ (it.next' h).toString.endPos := by
--   have lt : it.pos < it.toString.endPos := by
--     simp [hasNext] at h
--     exact h
--   simp [next'_eq_next, next_toString]
--   exact String.next_le_endPos it.toString it.pos lt

-- theorem lt_next (it : Iterator) : it.pos < it.next.pos := by
--   simp [pos, next]
--   exact String.Pos.Raw.byteIdx_lt_byteIdx_next _ _

-- theorem next_le_four (it : Iterator) : it.next.pos.byteIdx ≤ it.pos.byteIdx + 4 := by
--   show it.pos.byteIdx + Char.utf8Size (it.pos.get it.toString) ≤ it.pos.byteIdx + 4
--   simp [Char.utf8Size_le_four]

-- @[simp]
-- theorem next'_remainingBytes_lt {it : Iterator} {h : it.hasNext} : (it.next' h).remainingBytes < it.remainingBytes := by
--   simp only [hasNext, byteIdx_endPos, decide_eq_true_eq] at h
--   simp only [remainingBytes, next', Pos.Raw.next'_eq, Pos.Raw.next, byteIdx_endPos,
--     Pos.Raw.byteIdx_add_char]
--   have : (Pos.Raw.get it.s it.i).utf8Size > 0 := Char.utf8Size_pos _
--   grind

-- theorem curr'_eq_curr {it : Iterator} {h : it.hasNext} : it.curr' h = it.curr := by
--   simp [curr', curr]

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
