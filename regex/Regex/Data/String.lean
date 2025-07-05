namespace String

@[simp]
theorem utf8Size.go_append (cs₁ cs₂ : List Char) : utf8ByteSize.go (cs₁ ++ cs₂) = utf8ByteSize.go cs₁ + utf8ByteSize.go cs₂ := by
  induction cs₁ with
  | nil => simp [utf8ByteSize.go]
  | cons c cs₁ ih =>
    simp [utf8ByteSize.go, ih]
    omega

@[simp]
theorem utf8Size.go_nil : utf8ByteSize.go [] = 0 := rfl

@[simp]
theorem utf8Size.go_cons (c : Char) (cs : List Char) : utf8ByteSize.go (c :: cs) = utf8ByteSize.go cs + c.utf8Size := by
  simp [utf8ByteSize.go]

theorem next_le_endPosAux (p : Pos) (cs : List Char) (i ep : Pos) (lt : p < ep) (hep : ep = i + ⟨utf8ByteSize.go cs⟩) : p + utf8GetAux cs i p ≤ ep := by
  induction cs generalizing i with
  | nil =>
    simp [utf8GetAux, hep] at *
    exact Nat.succ_le_of_lt lt
  | cons c cs ih =>
    simp [utf8GetAux]
    split
    next eq =>
      rw [hep, eq]
      exact Nat.add_le_add_left (by simp) p.byteIdx
    next ne => exact ih (i + c) (by simp [hep, Pos.ext_iff, Nat.add_assoc, Nat.add_comm])

theorem next_le_endPos (s : String) (p : Pos) (lt : p < s.endPos) : s.next p ≤ s.endPos :=
  next_le_endPosAux p s.data 0 s.endPos lt (by simp [String.endPos, String.utf8ByteSize, Pos.ext_iff])

end String

namespace Char

def isWordChar (ch : Char) : Bool :=
  ch.isAlphanum || ch = '_'

end Char

namespace String.Iterator

open Char

def isCurrWord (it : Iterator) : Bool :=
  it.hasNext && isWordChar it.curr

def isPrevWord (it : Iterator) : Bool :=
  it.hasPrev && isWordChar it.prev.curr

def isAtWordBoundary (it : Iterator) : Bool :=
  isCurrWord it != isPrevWord it

def isAtNonWordBoundary (it : Iterator) : Bool :=
  isCurrWord it == isPrevWord it

theorem next'_eq_next (it : Iterator) (h : it.hasNext) : it.next' h = it.next := by
  simp [next', next]

theorem next_toString (it : Iterator) : it.next.toString = it.toString := by
  simp [next, toString]

theorem next_le_endPos (it : Iterator) (h : it.hasNext) : (it.next' h).pos ≤ (it.next' h).toString.endPos := by
  have lt : it.pos < it.toString.endPos := by
    simp [hasNext] at h
    exact h
  simp [next'_eq_next, next_toString]
  exact String.next_le_endPos it.toString it.pos lt

theorem lt_next (it : Iterator) : it.pos < it.next.pos := by
  simp [pos, next]
  exact String.lt_next _ _

theorem next_le_four (it : Iterator) : it.next.pos ≤ it.pos + ⟨4⟩ := by
  simp [pos, next, String.next]
  show it.pos.byteIdx + Char.utf8Size (it.toString.get it.pos) ≤ it.pos.byteIdx + 4
  simp [Char.utf8Size_le_four]

@[simp]
theorem next'_remainingBytes_lt {it : Iterator} {h : it.hasNext} : (it.next' h).remainingBytes < it.remainingBytes := by
  simp [hasNext] at h
  simp [next', remainingBytes, String.next]
  have : (it.s.get it.i).utf8Size > 0 := Char.utf8Size_pos _
  omega

theorem curr'_eq_curr {it : Iterator} {h : it.hasNext} : it.curr' h = it.curr := by
  simp [curr', curr]

end String.Iterator
