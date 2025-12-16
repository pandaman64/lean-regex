namespace Char

def isWordChar (ch : Char) : Bool :=
  ch.isAlphanum || ch = '_'

end Char

namespace Regex.Data.String

open Char
open _root_.String (Pos)

variable {s : String}

def isCurrWord (p : Pos s) : Bool :=
  if h : p ≠ s.endPos then
    isWordChar (p.get h)
  else
    false

def isPrevWord (p : Pos s) : Bool :=
  if h : p ≠ s.startPos then
    isWordChar ((p.prev h).get (by simp))
  else
    false

def isAtWordBoundary (p : Pos s) : Bool :=
  isCurrWord p != isPrevWord p

def isAtNonWordBoundary (p : Pos s) : Bool :=
  isCurrWord p == isPrevWord p

-- A simpler version of `String.Pos.find` that's easier to prove the correctness.
@[specialize]
def find (pos : Pos s) (p : Char → Bool) :=
  if hn : pos = s.endPos then
    pos
  else if p (pos.get hn) then
    pos
  else
    find (pos.next hn) p
termination_by pos

end Regex.Data.String

namespace String.Pos

theorem ne_endPos_of_lt {s : String} {pos pos' : Pos s} (lt : pos < pos') : pos ≠ s.endPos := by
  intro eq
  have : pos'.offset ≤ s.endPos.offset := pos'.isValid.le_rawEndPos
  exact Nat.not_le_of_lt (eq ▸ lt) this

@[grind ., simp]
theorem ne_next {s : String} {pos : Pos s} {ne : pos ≠ s.endPos} : pos ≠ pos.next ne := by
  intro eq
  have : pos.next ne < pos.next ne := eq ▸ pos.lt_next
  exact (Nat.lt_irrefl _ this).elim

def posRevInduction.{u} {s : String} {motive : Pos s → Sort u}
  (endPos : motive s.endPos)
  (next : ∀ p : Pos s, (h : p ≠ s.endPos) → motive (p.next h) → motive p)
  (p : Pos s) : motive p :=
  if h : p = s.endPos then
    h ▸ endPos
  else
    next p h (posRevInduction endPos next (p.next h))
  termination_by p

theorem splits_of_next {s l r : String} {p : Pos s} {h : p ≠ s.endPos}
  (sp : (p.next h).Splits (l ++ singleton (p.get h)) r) : p.Splits l (singleton (p.get h) ++ r) where
  eq_append := by simp only [sp.eq_append, String.append_assoc]
  offset_eq_rawEndPos := by simpa [Pos.next, Pos.Raw.ext_iff] using sp.offset_eq_rawEndPos

theorem splits_get_singleton {s l r : String} {c : Char} {p : Pos s} (sp : p.Splits l (singleton c ++ r)) :
  p.get sp.ne_endPos_of_singleton = c := by
  obtain ⟨r', h⟩ := sp.exists_eq_singleton_append sp.ne_endPos_of_singleton
  simp only [singleton_append_inj] at h
  exact h.1.symm

theorem lt_or_eq_of_le {s : String} {p p' : Pos s} (le : p ≤ p') : p < p' ∨ p = p' := by
  cases Nat.lt_or_eq_of_le le with
  | inl lt => exact .inl lt
  | inr eq => exact .inr (by simp [Pos.ext_iff, Pos.Raw.ext_iff, eq])

theorem Splits.exists_eq_append_left_of_lt {s l r : String} {p p' : Pos s} (sp : p.Splits l r) (lt : p' < p) :
  ∃ l₁ l₂, l = l₁ ++ l₂ ∧ p'.Splits l₁ (l₂ ++ r) := by
  induction p' using posRevInduction with
  | endPos => exact (Nat.not_lt_of_le p.isValid.le_rawEndPos lt).elim
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

theorem next_inj {s} {pos pos' : Pos s} {h : pos ≠ s.endPos} {h' : pos' ≠ s.endPos}
  (eq : pos.next h = pos'.next h') :
  pos = pos' := by
  have eq' := (pos.splits_next h).eq_left (eq ▸ pos'.splits_next h')
  simp only [append_singleton, push_inj] at eq'
  exact Pos.ext (Eq.trans (eq'.1 ▸ pos.splits.offset_eq_rawEndPos) (pos'.splits.offset_eq_rawEndPos).symm)

theorem le_of_lt_next {s} {pos pos' : Pos s} {h' : pos' ≠ s.endPos} (lt : pos < pos'.next h') : pos ≤ pos' :=
  Decidable.by_contra (fun nle => Nat.not_lt_of_le (Pos.next_le_of_lt (Nat.lt_of_not_le nle)) lt)

theorem le_or_eq_of_le_next {s} {pos pos' : Pos s} {h' : pos' ≠ s.endPos} (le : pos ≤ pos'.next h') :
  pos ≤ pos' ∨ pos = pos'.next h' :=
  Decidable.byCases
    (fun (eq : pos = pos'.next h') => .inr eq)
    (fun (ne : pos ≠ pos'.next h') => .inl (le_of_lt_next (lt_of_le_of_ne le ne)))

theorem le_next_iff {s} {pos pos' : Pos s} {h' : pos' ≠ s.endPos} :
  pos ≤ pos'.next h' ↔ pos ≤ pos' ∨ pos = pos'.next h' := by
  refine ⟨le_or_eq_of_le_next, ?_⟩
  intro h
  cases h with
  | inl le => exact Nat.le_trans le (Nat.le_of_lt pos'.lt_next)
  | inr eq => exact eq ▸ Nat.le_refl _

theorem lt_next_iff {s} {pos pos' : Pos s} {h' : pos' ≠ s.endPos} : pos < pos'.next h' ↔ pos ≤ pos' :=
  ⟨le_of_lt_next, fun le => Nat.lt_of_le_of_lt le pos'.lt_next⟩

theorem le_iff_lt_or_eq {s} {pos pos' : Pos s} : pos ≤ pos' ↔ pos < pos' ∨ pos = pos' :=
  Iff.trans Nat.le_iff_lt_or_eq (or_congr Iff.rfl (by simp [Pos.ext_iff, Pos.Raw.ext_iff]))

theorem lt_next_iff_lt_or_eq {s} {pos pos' : Pos s} (h' : pos' ≠ s.endPos) :
  pos < pos'.next h' ↔ pos < pos' ∨ pos = pos' :=
  lt_next_iff.trans le_iff_lt_or_eq

end String.Pos

namespace String

-- TODO: rename to `PosPlusOne`
@[ext]
structure ValidPosPlusOne (s : String) where
  offset : Pos.Raw
  isValidOrPlusOne : offset.IsValid s ∨ offset = s.rawEndPos.offsetBy ⟨1⟩
deriving Repr, DecidableEq

namespace ValidPosPlusOne

variable {s : String}

-- Doesn't seem to work at the moment
@[match_pattern]
def validPos (p : Pos s) : ValidPosPlusOne s :=
  ⟨p.offset, .inl p.isValid⟩

@[match_pattern]
def sentinel (s : String) : ValidPosPlusOne s :=
  ⟨s.rawEndPos.offsetBy ⟨1⟩, .inr rfl⟩

@[elab_as_elim, cases_eliminator]
def rec'.{u} {motive : ValidPosPlusOne s → Sort u}
  (validPos : (p : Pos s) → motive (validPos p))
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

instance : Inhabited (ValidPosPlusOne s) := ⟨.validPos s.startPos⟩

@[inline]
def isValid (p : ValidPosPlusOne s) : Bool :=
  p.offset ≠ s.rawEndPos.offsetBy ⟨1⟩

@[grind _=_]
theorem isValid_iff_isValid (p : ValidPosPlusOne s) : p.isValid ↔ p.offset.IsValid s := by
  cases p.isValidOrPlusOne with
  | inl h =>
    have ne : p.offset ≠ s.rawEndPos.offsetBy ⟨1⟩ :=
      have le : p.offset.byteIdx ≤ s.utf8ByteSize := h.le_utf8ByteSize
      have lt : p.offset.byteIdx < 1 + s.utf8ByteSize := by grind
      Pos.Raw.ne_of_lt (by simpa [Pos.Raw.lt_iff] using lt)
    simpa only [isValid, h, decide_eq_true_iff, iff_true] using ne
  | inr h =>
    have nv : ¬Pos.Raw.IsValid s (s.rawEndPos.offsetBy ⟨1⟩) := by
      intro v
      have := v.le_rawEndPos
      simp [Pos.Raw.le_iff] at this
      grind
    simpa [isValid, h]

def asValidPos (p : ValidPosPlusOne s) (h : p.isValid) : Pos s :=
  ⟨p.offset, p.isValid_iff_isValid.mp h⟩

def lt (p₁ p₂ : ValidPosPlusOne s) : Prop :=
  p₁.offset < p₂.offset

instance : LT (ValidPosPlusOne s) := ⟨lt⟩

theorem lt_iff {p₁ p₂ : ValidPosPlusOne s} : p₁ < p₂ ↔ p₁.offset < p₂.offset :=
  Iff.rfl

instance {s : String} (p₁ p₂ : ValidPosPlusOne s) : Decidable (p₁ < p₂) :=
  decidable_of_iff' _ lt_iff

def next (p : ValidPosPlusOne s) (h : p.isValid) : ValidPosPlusOne s :=
  let vp := p.asValidPos h
  if h' : vp ≠ s.endPos then
    .validPos (vp.next h')
  else
    .sentinel s

theorem lt_sentinel_of_valid {p : ValidPosPlusOne s} (h : p.isValid) : p < .sentinel s :=
  Nat.lt_of_le_of_lt (p.asValidPos h).isValid.le_rawEndPos (by simp [sentinel])

@[simp, grind →]
theorem lt_next (p : ValidPosPlusOne s) (h : p.isValid) : p < p.next h := by
  fun_cases next
  next vp ne => exact Pos.lt_next (p := p.asValidPos h) (h := ne)
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

def le (p₁ p₂ : ValidPosPlusOne s) : Prop :=
  p₁.offset ≤ p₂.offset

instance : LE (ValidPosPlusOne s) := ⟨le⟩

@[grind =]
theorem le_iff {p₁ p₂ : ValidPosPlusOne s} : p₁ ≤ p₂ ↔ p₁.offset ≤ p₂.offset :=
  Iff.rfl

@[simp, grind =]
theorem validPos_le_validPos_iff {p₁ p₂ : Pos s} : ValidPosPlusOne.validPos p₁ ≤ ValidPosPlusOne.validPos p₂ ↔ p₁ ≤ p₂ :=
  Iff.rfl

instance {s : String} (p₁ p₂ : ValidPosPlusOne s) : Decidable (p₁ ≤ p₂) :=
  decidable_of_iff' _ le_iff

theorem isValid_of_isValid_of_le {p₁ p₂ : ValidPosPlusOne s} (h : p₂.isValid) (le : p₁ ≤ p₂) : p₁.isValid := by
  cases p₁.isValidOrPlusOne with
  | inl h₁ => simpa [p₁.isValid_iff_isValid] using h₁
  | inr h₁ =>
    rw [p₂.isValid_iff_isValid] at h
    have le' : p₂.offset ≤ s.rawEndPos := h.le_rawEndPos
    have le'' : s.rawEndPos.offsetBy ⟨1⟩ ≤ s.rawEndPos := h₁ ▸ Pos.Raw.le_trans le le'
    simp [Pos.Raw.le_iff] at le''
    grind

@[grind .]
theorem validPos_inj {p₁ p₂ : Pos s} (h : ValidPosPlusOne.validPos p₁ = ValidPosPlusOne.validPos p₂) : p₁ = p₂ := by
  simp only [validPos, ValidPosPlusOne.mk.injEq] at h
  exact Pos.ext h

def or (p₁ p₂ : ValidPosPlusOne s) : ValidPosPlusOne s :=
  if p₁.isValid then
    p₁
  else
    p₂

def orElse (p₁ : ValidPosPlusOne s) (p₂ : Unit → ValidPosPlusOne s) : ValidPosPlusOne s :=
  if p₁.isValid then
    p₁
  else
    p₂ ()

instance : OrElse (ValidPosPlusOne s) := ⟨orElse⟩

@[simp, grind =]
theorem orElse_eq_or {p₁ : ValidPosPlusOne s} {p₂} : p₁.orElse p₂ = p₁.or (p₂ ()) := by
  grind [orElse, or]

@[simp, grind =]
theorem hOrElse_eq_orElse {p₁ : ValidPosPlusOne s} {p₂} : HOrElse.hOrElse p₁ p₂ = p₁.orElse p₂ := rfl

@[simp, grind =]
theorem or_valid {p₁ p₂ : ValidPosPlusOne s} (h : p₁.isValid) : p₁.or p₂ = p₁ := by
  simp [or, h]

@[simp, grind =]
theorem or_not_valid {p₁ p₂ : ValidPosPlusOne s} (h : ¬p₁.isValid) : p₁.or p₂ = p₂ := by
  simp [or, h]

@[simp, grind =]
theorem isValid_validPos {p : Pos s} : (ValidPosPlusOne.validPos p).isValid = true :=
  (isValid_iff_isValid (.validPos p)).mpr p.isValid

@[simp, grind =]
theorem not_isValid_sentinel {s : String} : (ValidPosPlusOne.sentinel s).isValid = false := by
  simp [sentinel, isValid]

@[simp, grind =]
theorem sentinel_or {p₁ p₂ : ValidPosPlusOne s} (h : p₁ = .sentinel s) : p₁.or p₂ = p₂ := by
  grind

@[simp, grind =>]
theorem validPos_or {p₁ p₂ : ValidPosPlusOne s} (h : p₁ = .validPos p) : p₁.or p₂ = p₁ := by
  grind

@[simp, grind =]
theorem or_sentinel {p₁ p₂ : ValidPosPlusOne s} (h : p₂ = .sentinel s) : p₁.or p₂ = p₁ := by
  cases p₁ with
  | validPos p => simp
  | sentinel => simp [h]

@[grind .]
theorem validPos_ne_sentinel {p : Pos s} : ValidPosPlusOne.validPos p ≠ ValidPosPlusOne.sentinel s := by
  intro eq
  have : isValid (.validPos p) = isValid (.sentinel s) := by grind
  simp at this

@[simp, grind =]
theorem or_self {p : ValidPosPlusOne s} : p.or p = p := by
  cases p with
  | validPos p => simp
  | sentinel => simp

@[simp, grind =]
theorem asValidPos_validPos {p : Pos s} : (ValidPosPlusOne.validPos p).asValidPos (by grind) = p := rfl

@[simp, grind =]
theorem validPos_asValidPos {p : ValidPosPlusOne s} {h : p.isValid} : (ValidPosPlusOne.validPos (p.asValidPos h)) = p := rfl

end ValidPosPlusOne

def startValidPosPlusOne (s : String) : ValidPosPlusOne s :=
  .validPos s.startPos

end String
