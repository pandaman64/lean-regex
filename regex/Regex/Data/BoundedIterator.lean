import Regex.Data.String

set_option autoImplicit false

open String (Iterator)

namespace Regex.Data

@[ext]
structure BoundedIterator (startIdx maxIdx : Nat) where
  it : Iterator
  ge : startIdx ≤ it.pos.byteIdx
  le : it.pos.byteIdx ≤ maxIdx
  eq : maxIdx = it.toString.endPos.byteIdx

namespace BoundedIterator

variable {startIdx maxIdx : Nat}

def toString (bit : BoundedIterator startIdx maxIdx) : String := bit.it.toString

def pos (bit : BoundedIterator startIdx maxIdx) : String.Pos := bit.it.pos

def index (bit : BoundedIterator startIdx maxIdx) : Fin (maxIdx + 1 - startIdx) :=
  have lt : bit.it.pos.byteIdx - startIdx < maxIdx + 1 - startIdx := by
    exact Nat.sub_lt_sub_right bit.ge (Nat.lt_of_le_of_lt bit.le (Nat.lt_succ_self _))
  ⟨bit.it.pos.byteIdx - startIdx, lt⟩

def hasNext (bit : BoundedIterator startIdx maxIdx) : Bool := bit.it.hasNext

def next (bit : BoundedIterator startIdx maxIdx) (h : bit.hasNext) : BoundedIterator startIdx maxIdx :=
  let it' := bit.it.next' h
  have ge' : startIdx ≤ it'.pos.byteIdx := Nat.le_of_lt (Nat.lt_of_le_of_lt bit.ge bit.it.lt_next)
  have eq' : maxIdx = it'.toString.endPos.byteIdx :=
    calc maxIdx
      _ = bit.it.toString.endPos.byteIdx := bit.eq
      _ = it'.toString.endPos.byteIdx := by simp [it', Iterator.next', Iterator.toString]
  have le' : it'.pos.byteIdx ≤ maxIdx := eq' ▸ bit.it.next_le_endPos h
  ⟨it', ge', le', eq'⟩

def nextn (bit : BoundedIterator startIdx maxIdx) (n : Nat) : BoundedIterator startIdx maxIdx :=
  match n with
  | 0 => bit
  | n + 1 =>
    if h : bit.hasNext then
      nextn (bit.next h) n
    else
      bit

def IsNextNOf (bit bit₀ : BoundedIterator startIdx maxIdx) : Prop := ∃ n, bit = bit₀.nextn n

def curr (bit : BoundedIterator startIdx maxIdx) (h : bit.hasNext) : Char := bit.it.curr' h

def remainingBytes (bit : BoundedIterator startIdx maxIdx) : Nat := bit.it.remainingBytes

theorem next_remainingBytes_lt (bit : BoundedIterator startIdx maxIdx) (h : bit.hasNext) : (bit.next h).remainingBytes < bit.remainingBytes := by
  simp [next, remainingBytes]

def Valid (bit : BoundedIterator startIdx maxIdx) : Prop := String.Pos.isValid bit.it.toString bit.it.pos

end BoundedIterator

end Regex.Data
