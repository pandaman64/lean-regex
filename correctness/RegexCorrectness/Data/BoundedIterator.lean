import Regex.Data.BoundedIterator
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (Iterator)

namespace Regex.Data.BoundedIterator

variable {startIdx maxIdx : Nat}

@[ext]
theorem ext_pos {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (h₁ : bit₁.toString = bit₂.toString) (h₂ : bit₁.pos = bit₂.pos) : bit₁ = bit₂ := by
  simp [BoundedIterator.ext_iff, Iterator.ext_iff]
  exact ⟨h₁, h₂⟩

@[ext]
theorem ext_index {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (h₁ : bit₁.toString = bit₂.toString) (h₂ : bit₁.index = bit₂.index) : bit₁ = bit₂ := by
  simp [BoundedIterator.ext_pos_iff, h₁]
  simp [index, String.Pos.ext_iff] at h₂
  simp [String.Pos.ext_iff]
  calc bit₁.pos.byteIdx
    _ = bit₂.pos.byteIdx - startIdx + startIdx := Nat.eq_add_of_sub_eq bit₁.ge h₂
    _ = bit₂.pos.byteIdx := Nat.sub_add_cancel bit₂.ge

theorem next_toString {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) : (bit.next h).toString = bit.toString := by
  simp [next, Iterator.next', BoundedIterator.toString]

theorem byteIdx_lt_next_byteIdx {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) : bit.pos.byteIdx < (bit.next h).pos.byteIdx := by
  simp [next, pos, Iterator.next'_eq_next]
  exact String.Iterator.lt_next bit.it

theorem pos_lt_next_pos {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) : bit.pos < (bit.next h).pos := byteIdx_lt_next_byteIdx h

theorem valid_of_it_valid {bit : BoundedIterator startIdx maxIdx} (v : bit.it.Valid) : bit.Valid := v.isValid

theorem valid_of_valid {bit : BoundedIterator startIdx maxIdx} (v : bit.Valid) : bit.it.Valid := Iterator.Valid.of_isValid v

theorem next_valid {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) (v : bit.Valid) : (bit.next h).Valid := by
  apply valid_of_it_valid
  simp [next, String.Iterator.next'_eq_next]
  exact (bit.valid_of_valid v).next h

theorem nextn_valid {bit : BoundedIterator startIdx maxIdx} {n : Nat} (v : bit.Valid) : (bit.nextn n).Valid := by
  induction n generalizing bit with
  | zero => simpa [nextn] using v
  | succ n ih =>
    if h : bit.hasNext then
      simp [nextn, h]
      exact ih (bit.next_valid h v)
    else
      simpa [nextn, h] using v

theorem next_nextn {bit : BoundedIterator startIdx maxIdx} {n : Nat} (hnext : bit.hasNext) : (bit.next hnext).nextn n = bit.nextn (n + 1) := by
  cases n with
  | zero => simp [nextn, hnext]
  | succ n => simp [nextn, hnext]

theorem byteIdx_le_nextn_byteIdx (bit : BoundedIterator startIdx maxIdx) (n : Nat) : bit.pos.byteIdx ≤ (bit.nextn n).pos.byteIdx := by
  induction n generalizing bit with
  | zero => simp [nextn]
  | succ n ih =>
    simp [nextn]
    if h : bit.hasNext then
      simp [nextn, h]
      exact Nat.le_of_lt (Nat.lt_of_lt_of_le (byteIdx_lt_next_byteIdx h) (ih (bit.next h)))
    else
      simp [nextn, h]

theorem nextn_toString {bit : BoundedIterator startIdx maxIdx} {n : Nat} : (bit.nextn n).toString = bit.toString := by
  induction n generalizing bit with
  | zero => simp [nextn]
  | succ n ih =>
    if h : bit.hasNext then
      simp [nextn, h, ih, next_toString]
    else
      simp [nextn, h]

theorem hasNext_of_nextn_hasNext {bit : BoundedIterator startIdx maxIdx} {n : Nat} (hnext : (bit.nextn n).hasNext) : bit.hasNext := by
  have le : bit.pos.byteIdx ≤ (bit.nextn n).pos.byteIdx := bit.byteIdx_le_nextn_byteIdx n
  have lt : (bit.nextn n).pos.byteIdx < bit.toString.endPos.byteIdx := by
    have : (bit.nextn n).pos.byteIdx < (bit.nextn n).toString.endPos.byteIdx := by
      simp [hasNext, Iterator.hasNext] at hnext
      exact hnext
    simpa [nextn_toString]
  show decide (bit.pos.byteIdx < bit.toString.endPos.byteIdx) = true
  simp
  omega

theorem nextn_next_eq_next_nextn {bit : BoundedIterator startIdx maxIdx} {n : Nat} (hnext : (bit.nextn n).hasNext) : (bit.nextn n).next hnext = (bit.next (hasNext_of_nextn_hasNext hnext)).nextn n := by
  induction n generalizing bit with
  | zero => simp [nextn]
  | succ n ih =>
    have hnext₀ : bit.hasNext := hasNext_of_nextn_hasNext hnext
    simp [nextn, hnext₀] at hnext
    have hnext₁ : (bit.next hnext₀).hasNext := hasNext_of_nextn_hasNext hnext
    simp [nextn, hnext₀, hnext₁]
    exact ih hnext

theorem nextn_next {bit : BoundedIterator startIdx maxIdx} {n : Nat} (hnext : (bit.nextn n).hasNext) : (bit.nextn n).next hnext = bit.nextn (n + 1) := by
  rw [nextn_next_eq_next_nextn hnext, next_nextn]

theorem nextn_not_hasNext {bit : BoundedIterator startIdx maxIdx} {n : Nat} (hnext : ¬bit.hasNext) : (bit.nextn n) = bit := by
  cases n with
  | zero => simp [nextn]
  | succ n => simp [nextn, hnext]

theorem nextn_add (bit : BoundedIterator startIdx maxIdx) (n₁ n₂ : Nat) : bit.nextn (n₁ + n₂) = (bit.nextn n₁).nextn n₂ := by
  induction n₁ generalizing bit with
  | zero => simp [nextn]
  | succ n₁ ih =>
    have : n₁ + 1 + n₂ = (n₁ + n₂) + 1 := by omega
    if hnext : bit.hasNext then
      simpa [nextn, this, hnext] using ih (bit.next hnext)
    else
      simp [nextn, this, hnext, nextn_not_hasNext hnext]

def ValidFor (l r : List Char) (bit : BoundedIterator startIdx maxIdx) : Prop := bit.it.ValidFor l r

namespace ValidFor

theorem hasNext {l r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l r bit) : bit.hasNext ↔ r ≠ [] := by
  unfold ValidFor at vf
  exact vf.hasNext

theorem next {l c r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l (c :: r) bit) : ValidFor (c :: l) r (bit.next (by simp [vf.hasNext])) := by
  unfold ValidFor at vf
  exact vf.next

theorem next' {l r} {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) (vf : ValidFor l r bit) : ∃ c r', r = c :: r' ∧ ValidFor (c :: l) r' (bit.next h) := by
  match r with
  | [] => simp [vf.hasNext] at h
  | c :: r' => exact ⟨c, r', rfl, vf.next⟩

theorem curr {l c r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l (c :: r) bit) : bit.curr (by simp [vf.hasNext]) = c := by
  simp [BoundedIterator.curr, bit.it.curr'_eq_curr, String.Iterator.ValidFor.curr vf]

theorem toString {l r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l r bit) : bit.toString = ⟨l.reverse ++ r⟩ := by
  simp [ValidFor] at vf
  simpa [toString] using vf.toString

theorem valid {l r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l r bit) : bit.Valid := by
  simp [ValidFor] at vf
  exact valid_of_it_valid vf.valid

theorem eq {l l' r r'} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l r bit) (vf' : ValidFor l' r' bit) : l = l' ∧ r = r' :=
  Iterator.ValidFor.eq vf vf'

theorem eq_it {l r} {bit bit' : BoundedIterator startIdx maxIdx} (vf : ValidFor l r bit) (vf' : ValidFor l r bit') : bit = bit' :=
  BoundedIterator.ext (Iterator.ValidFor.eq_it vf vf')

end ValidFor

namespace Valid

theorem validFor {bit : BoundedIterator startIdx maxIdx} (v : bit.Valid) : ∃ l r, ValidFor l r bit :=
  (bit.valid_of_valid v).validFor

theorem validFor_of_hasNext {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) (v : bit.Valid) :
  ∃ l r, ValidFor l (bit.curr h :: r) bit := by
  have ⟨l, r, vf⟩ := validFor v
  match h' : r with
  | [] => simp [vf.hasNext] at h
  | c :: r' => exact ⟨l, r', by simpa [vf.curr] using vf⟩

theorem next {bit : BoundedIterator startIdx maxIdx} (hnext : bit.hasNext) (v : bit.Valid) : (bit.next hnext).Valid := by
have ⟨l, r, vf⟩ := v.validFor_of_hasNext hnext
exact vf.next.valid

end Valid

theorem eq_of_valid_of_next_eq {bit bit' : BoundedIterator startIdx maxIdx} (v : bit.Valid) (v' : bit'.Valid) (hnext : bit.hasNext) (hnext' : bit'.hasNext) (eq : bit.next hnext = bit'.next hnext') : bit = bit' := by
  have ⟨l, r, vf⟩ := v.validFor_of_hasNext hnext
  have vfn := vf.next
  have ⟨l', r', vf'⟩ := v'.validFor_of_hasNext hnext'
  have vfn' := vf'.next

  have eqs : bit.curr hnext :: l = bit'.curr hnext' :: l' ∧ r = r' := vfn.eq (eq ▸ vfn')
  simp at eqs
  simp [eqs] at vf

  exact vf.eq_it vf'

inductive Reaches (bit : BoundedIterator startIdx maxIdx) : BoundedIterator startIdx maxIdx → Prop
| refl (v : bit.Valid) : Reaches bit bit
| next {bit' : BoundedIterator startIdx maxIdx} (h : bit.Reaches bit') (hnext : bit'.hasNext) : Reaches bit (bit'.next hnext)

namespace Reaches

theorem trans {bit₁ bit₂ bit₃ : BoundedIterator startIdx maxIdx} (h₁ : Reaches bit₁ bit₂) (h₂ : Reaches bit₂ bit₃) : Reaches bit₁ bit₃ := by
  induction h₂ with
  | refl => exact h₁
  | @next bit' _ hnext ih => exact ih.next hnext

theorem validL {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (h : Reaches bit₁ bit₂) : bit₁.Valid := by
  induction h with
  | refl v => exact v
  | next _ _ ih => exact ih

theorem validR {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (h : Reaches bit₁ bit₂) : bit₂.Valid := by
  induction h with
  | refl v => exact v
  | next _ hnext ih => exact ih.next hnext

theorem toString {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (h : Reaches bit₁ bit₂) : bit₂.toString = bit₁.toString := by
  induction h with
  | refl => rfl
  | next _ _ ih => simp [next_toString, ih]

theorem le_pos {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (h : Reaches bit₁ bit₂) : bit₁.pos ≤ bit₂.pos := by
  induction h with
  | refl v => exact Nat.le_refl _
  | next _ hnext ih => exact Nat.le_of_lt (Nat.lt_of_le_of_lt ih (byteIdx_lt_next_byteIdx hnext))

theorem next_iff' {bit₁ bit₂ bit₂' : BoundedIterator startIdx maxIdx} (v : bit₂.Valid) (hnext : bit₂.hasNext) (eq : bit₂' = bit₂.next hnext) : bit₁.Reaches bit₂' ↔ bit₁.Reaches bit₂ ∨ (bit₁.Valid ∧ bit₁ = bit₂') := by
  apply Iff.intro
  . intro h
    cases h with
    | refl v => exact .inr ⟨v, rfl⟩
    | @next bit₂' h hnext' =>
      have eq : bit₂' = bit₂ := eq_of_valid_of_next_eq h.validR v hnext' hnext eq
      exact .inl (eq ▸ h)
  . intro h
    match h with
    | .inl h => exact eq ▸ h.next hnext
    | .inr ⟨v, eq'⟩ => exact eq' ▸ .refl v

@[simp]
theorem next_iff {bit₁ bit₂ : BoundedIterator startIdx maxIdx} (v : bit₂.Valid) (hnext : bit₂.hasNext) : bit₁.Reaches (bit₂.next hnext) ↔ bit₁.Reaches bit₂ ∨ (bit₁.Valid ∧ bit₁ = bit₂.next hnext) :=
  next_iff' v hnext rfl

end Reaches

def BetweenI (bit bs be : BoundedIterator startIdx maxIdx) : Prop := bs.Reaches bit ∧ bit.Reaches be

def BetweenE (bit bs be : BoundedIterator startIdx maxIdx) : Prop := bit.pos < be.pos ∧ bit.BetweenI bs be

namespace BetweenI

variable {bit bs be : BoundedIterator startIdx maxIdx}

theorem reachesSE (h : bit.BetweenI bs be) : bs.Reaches be := h.1.trans h.2

theorem le_pos (h : bit.BetweenI bs be) : bit.pos ≤ be.pos := h.2.le_pos

@[simp]
theorem next_iff (v : be.Valid) (hnext : be.hasNext) : bit.BetweenI bs (be.next hnext) ↔ bit.BetweenI bs be ∨ (bs.Reaches bit ∧ bit = be.next hnext) := by
  simp [BetweenI, v, hnext, ←and_or_left]
  intro h
  simp [h.validR]

theorem iffE : bit.BetweenI bs be ↔ bit.BetweenE bs be ∨ (bs.Reaches bit ∧ bit = be) := by
  apply Iff.intro
  . intro h
    if lt : bit.pos < be.pos then
      exact .inl ⟨lt, h⟩
    else
      have eq_pos : bit.pos = be.pos := by
        simp [String.Pos.ext_iff]
        exact Nat.le_antisymm (le_pos h) (Nat.le_of_not_lt lt)
      have eq : bit = be := by
        simp [BoundedIterator.ext_pos_iff, eq_pos, h.2.toString]
      exact .inr ⟨h.1, eq⟩
  . intro h
    match h with
    | .inl ⟨lt, h⟩ => exact h
    | .inr ⟨h, eq⟩ => exact ⟨h, eq ▸ .refl h.validR⟩

end BetweenI

namespace BetweenE

variable {bit bs be : BoundedIterator startIdx maxIdx}

theorem validE (h : bit.BetweenE bs be) : be.Valid := h.2.2.validR

theorem ne_end (h : bit.BetweenE bs be) : bit ≠ be := by
  intro eq
  have lt : bit.pos < be.pos := h.1
  simp only [eq, String.pos_lt_eq, Nat.lt_irrefl] at lt

theorem next_iffI (v : be.Valid) (hnext : be.hasNext) : bit.BetweenE bs (be.next hnext) ↔ bit.BetweenI bs be := by
  simp [BetweenE, v, hnext, -String.pos_lt_eq]
  apply Iff.intro
  . intro ⟨lt, h⟩
    match h with
    | .inl h => exact h
    | .inr ⟨_, eq⟩ => simp only [eq, String.pos_lt_eq, Nat.lt_irrefl] at lt
  . intro h
    exact ⟨Nat.lt_of_le_of_lt (h.le_pos) (pos_lt_next_pos hnext), .inl h⟩

@[simp]
theorem next_iff (v : be.Valid) (hnext : be.hasNext) : bit.BetweenE bs (be.next hnext) ↔ bit.BetweenE bs be ∨ (bs.Reaches bit ∧ bit = be) := by
  simp [next_iffI v hnext, BetweenI.iffE]

end BetweenE

end Regex.Data.BoundedIterator
