import Regex.Data.BoundedIterator
import RegexCorrectness.Data.String

open String (Iterator)

namespace Regex.Data.BoundedIterator

theorem valid_of_it_valid {startIdx} (bit : BoundedIterator startIdx) (v : bit.it.Valid) : bit.Valid := v.isValid

theorem valid_of_valid {startIdx} (bit : BoundedIterator startIdx) (v : bit.Valid) : bit.it.Valid := Iterator.Valid.of_isValid v

theorem next_valid {startIdx} (bit : BoundedIterator startIdx) (h : bit.hasNext) (v : bit.Valid) : (bit.next h).Valid := by
  apply valid_of_it_valid
  simp [next, String.Iterator.next'_eq_next]
  exact (bit.valid_of_valid v).next h

end Regex.Data.BoundedIterator
