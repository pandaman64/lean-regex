import Regex.Data.BoundedIterator
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (Iterator)

namespace Regex.Data.BoundedIterator

theorem valid_of_it_valid {startIdx} (bit : BoundedIterator startIdx) (v : bit.it.Valid) : bit.Valid := v.isValid

theorem valid_of_valid {startIdx} (bit : BoundedIterator startIdx) (v : bit.Valid) : bit.it.Valid := Iterator.Valid.of_isValid v

theorem next_valid {startIdx} (bit : BoundedIterator startIdx) (h : bit.hasNext) (v : bit.Valid) : (bit.next h).Valid := by
  apply valid_of_it_valid
  simp [next, String.Iterator.next'_eq_next]
  exact (bit.valid_of_valid v).next h

def ValidFor {startIdx} (l r : List Char) (bit : BoundedIterator startIdx) : Prop := bit.it.ValidFor l r

namespace ValidFor

theorem hasNext {startIdx l r} {bit : BoundedIterator startIdx} (vf : ValidFor l r bit) : bit.hasNext ↔ r ≠ [] := by
  unfold ValidFor at vf
  exact vf.hasNext

theorem next {startIdx l c r} {bit : BoundedIterator startIdx} (vf : ValidFor l (c :: r) bit) : ValidFor (c :: l) r (bit.next (by simp [vf.hasNext])) := by
  unfold ValidFor at vf
  exact vf.next

theorem next' {startIdx l r} {bit : BoundedIterator startIdx} (h : bit.hasNext) (vf : ValidFor l r bit) : ∃ c r', ValidFor (c :: l) r' (bit.next h) := by
  match r with
  | [] => simp [vf.hasNext] at h
  | c :: r' => exact ⟨c, r', vf.next⟩

theorem curr {startIdx l c r} {bit : BoundedIterator startIdx} (vf : ValidFor l (c :: r) bit) : bit.curr (by simp [vf.hasNext]) = c := by
  simp [BoundedIterator.curr, bit.it.curr'_eq_curr, String.Iterator.ValidFor.curr vf]

end ValidFor

namespace Valid

theorem validFor {startIdx} {bit : BoundedIterator startIdx} (v : bit.Valid) : ∃ l r, ValidFor l r bit :=
  (bit.valid_of_valid v).validFor

theorem validFor_of_hasNext {startIdx} {bit : BoundedIterator startIdx} (h : bit.hasNext) (v : bit.Valid) :
  ∃ l r, ValidFor l (bit.curr h :: r) bit := by
  have ⟨l, r, vf⟩ := validFor v
  match h' : r with
  | [] => simp [vf.hasNext] at h
  | c :: r' => exact ⟨l, r', by simpa [vf.curr] using vf⟩

end Valid

end Regex.Data.BoundedIterator
