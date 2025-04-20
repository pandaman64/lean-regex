import Regex.Data.String

set_option autoImplicit false

open String (Iterator)

namespace Regex.Data

structure BoundedIterator (startIdx : Nat) where
  it : Iterator
  ge : startIdx ≤ it.pos.byteIdx
  le : it.pos ≤ it.toString.endPos

namespace BoundedIterator

def maxIdx {startIdx : Nat} (bit : BoundedIterator startIdx) : Nat := bit.it.toString.endPos.byteIdx

def pos {startIdx : Nat} (bit : BoundedIterator startIdx) : String.Pos := bit.it.pos

def index {startIdx : Nat} (bit : BoundedIterator startIdx) : Fin (bit.maxIdx + 1 - startIdx) :=
  have lt : bit.it.pos.byteIdx - startIdx < bit.maxIdx + 1 - startIdx := by
    exact Nat.sub_lt_sub_right bit.ge (Nat.lt_of_le_of_lt bit.le (Nat.lt_succ_self _))
  ⟨bit.it.pos.byteIdx - startIdx, lt⟩

def index' {startIdx maxIdx : Nat} (bit : BoundedIterator startIdx) (h : bit.maxIdx = maxIdx) : Fin (maxIdx + 1 - startIdx) :=
  bit.index.cast (by simp [h])

def hasNext {startIdx : Nat} (bit : BoundedIterator startIdx) : Bool := bit.it.hasNext

def next {startIdx : Nat} (bit : BoundedIterator startIdx) (h : bit.hasNext) : BoundedIterator startIdx :=
  let it' := bit.it.next' h
  have ge' : startIdx ≤ it'.pos.byteIdx := Nat.le_of_lt (Nat.lt_of_le_of_lt bit.ge bit.it.lt_next)
  have le' : it'.pos ≤ it'.toString.endPos := bit.it.next_le_endPos h
  ⟨it', ge', le'⟩

def curr {startIdx : Nat} (bit : BoundedIterator startIdx) (h : bit.hasNext) : Char := bit.it.curr' h

theorem next_maxIdx {startIdx : Nat} (bit : BoundedIterator startIdx) (h : bit.hasNext) : (bit.next h).maxIdx = bit.maxIdx := rfl

def remainingBytes {startIdx : Nat} (bit : BoundedIterator startIdx) : Nat := bit.it.remainingBytes

theorem next_remainingBytes_lt {startIdx : Nat} (bit : BoundedIterator startIdx) (h : bit.hasNext) : (bit.next h).remainingBytes < bit.remainingBytes := by
  simp [next, remainingBytes]

def Valid {startIdx : Nat} (bit : BoundedIterator startIdx) : Prop := String.Pos.isValid bit.it.toString bit.it.pos

end BoundedIterator

end Regex.Data
