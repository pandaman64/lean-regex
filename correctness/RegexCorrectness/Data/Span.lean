import RegexCorrectness.Data.String

set_option autoImplicit false

open String (Pos Iterator)
open String.Iterator (ValidFor)

namespace Regex.Data

structure Span where
  l : List Char
  m : List Char
  r : List Char

namespace Span

def curr (s : Span) : Pos := ⟨String.utf8Len s.l + String.utf8Len s.m⟩

def atEnd (s : Span) : Bool := s.r = []

def next (s : Span) : Span := ⟨s.l, s.r.headD default :: s.m, s.r.tail⟩

theorem next_eq {s : Span} {c r'} (h : s.r = c :: r') : s.next = ⟨s.l, c :: s.m, r'⟩ := by
  simp [Span.next, h]

theorem next_eq' {s : Span} {l m c r'} (h : s = ⟨l, m, c :: r'⟩) : s.next = ⟨l, c :: m, r'⟩ := by
  simp [Span.next, h]

theorem next_curr {s : Span} {c r'} (h : s.r = c :: r') : s.next.curr = s.curr + c := by
  simp [Span.next_eq h, Span.curr, Pos.ext_iff]
  omega

def toString (s : Span) : String := ⟨s.l ++ s.m.reverse ++ s.r⟩

def iterator (s : Span) : Iterator := ⟨s.toString, s.curr⟩

theorem validFor (s : Span) : ValidFor (s.m ++ s.l.reverse) s.r s.iterator := by
  simp [Span.iterator, Span.toString, Span.curr]
  apply ValidFor.of_eq
  . simp
  . simp
    omega

theorem exists_cons_of_not_atEnd {s : Span} (h : ¬s.iterator.atEnd) : ∃ r', s.r = s.iterator.curr :: r' :=
  s.validFor.exists_cons_of_not_atEnd h

theorem exists_cons_of_curr' {s : Span} {c} (h : s.iterator.hasNext) (eq : s.iterator.curr' h = c) : ∃ r', s.r = c :: r' := by
  have ⟨r', eqr⟩ := s.exists_cons_of_not_atEnd (by simpa [Iterator.atEnd, Iterator.hasNext] using h)
  have eq' : s.iterator.curr' h = s.iterator.curr := rfl
  rw [←eq', eq] at eqr
  exact ⟨r', eqr⟩

theorem curr_eq_pos {s : Span} : s.curr = s.iterator.pos := rfl

theorem next_curr_eq_next_pos {s : Span} {c r'} (h : s.r = c :: r') : s.next.curr = s.iterator.next.pos := by
  have := (h ▸ s.validFor).next.pos
  simp at this
  rw [Span.next_curr h, Span.curr]
  simp [this, Pos.ext_iff]
  omega

theorem eq_of_iterator_validFor {s : Span} {ml r} (v : s.iterator.ValidFor ml r) :
  ml = s.m ++ s.l.reverse ∧ r = s.r := by
  have v' := s.validFor
  exact v.eq v'

theorem next_toString {s : Span} {c r'} (h : s.r = c :: r') : s.next.toString = s.toString := by
  rw [Span.next_eq h]
  unfold Span.toString
  simp [h]

theorem next_iterator {s : Span} {c r'} (h : s.r = c :: r') : s.next.iterator = s.iterator.next := by
  rw [Span.iterator, Span.next_curr_eq_next_pos h, Span.next_toString h, Iterator.ext_iff]
  simp [Span.iterator]
  rfl

theorem next_iterator' {s : Span} {l m c r'} (h : s = ⟨l, m, c :: r'⟩) : s.next.iterator = s.iterator.next := by
  exact next_iterator (c := c) (r' := r') (by simp [h])

end Span

end Regex.Data
