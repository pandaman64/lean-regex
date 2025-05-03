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

namespace IsNextNOf

@[simp]
theorem rfl {bit : BoundedIterator startIdx maxIdx} : bit.IsNextNOf bit := ⟨0, by simp [nextn]⟩

theorem toString {bit bit₀ : BoundedIterator startIdx maxIdx} (h : bit.IsNextNOf bit₀) : bit.toString = bit₀.toString := by
  have ⟨n, eq⟩ := h
  simp [eq, nextn_toString]

theorem hasNext_of_hasNext {bit bit₀ : BoundedIterator startIdx maxIdx} (h : bit.IsNextNOf bit₀) (hnext : bit.hasNext) : bit₀.hasNext := by
  have ⟨n, eq⟩ := h
  cases n with
  | zero => simpa [eq] using hnext
  | succ n =>
    if hnext₀ : bit₀.hasNext then
      exact hnext₀
    else
      simp [nextn, hnext₀] at eq
      simpa [eq] using hnext

theorem next {bit bit₀ : BoundedIterator startIdx maxIdx} (h : bit.IsNextNOf bit₀) (hnext : bit.hasNext) : (bit.next hnext).IsNextNOf bit₀ := by
  have ⟨n, eq⟩ := h
  exact ⟨n + 1, by simp [eq, nextn_next]⟩

theorem valid {bit bit₀ : BoundedIterator startIdx maxIdx} (h : bit.IsNextNOf bit₀) (v₀ : bit₀.Valid) : bit.Valid := by
  have ⟨n, eq⟩ := h
  rw [eq]
  exact nextn_valid v₀

end IsNextNOf

def ValidFor (l r : List Char) (bit : BoundedIterator startIdx maxIdx) : Prop := bit.it.ValidFor l r

namespace ValidFor

theorem hasNext {l r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l r bit) : bit.hasNext ↔ r ≠ [] := by
  unfold ValidFor at vf
  exact vf.hasNext

theorem next {l c r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l (c :: r) bit) : ValidFor (c :: l) r (bit.next (by simp [vf.hasNext])) := by
  unfold ValidFor at vf
  exact vf.next

theorem next' {l r} {bit : BoundedIterator startIdx maxIdx} (h : bit.hasNext) (vf : ValidFor l r bit) : ∃ c r', ValidFor (c :: l) r' (bit.next h) := by
  match r with
  | [] => simp [vf.hasNext] at h
  | c :: r' => exact ⟨c, r', vf.next⟩

theorem curr {l c r} {bit : BoundedIterator startIdx maxIdx} (vf : ValidFor l (c :: r) bit) : bit.curr (by simp [vf.hasNext]) = c := by
  simp [BoundedIterator.curr, bit.it.curr'_eq_curr, String.Iterator.ValidFor.curr vf]

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

end Valid

end Regex.Data.BoundedIterator
