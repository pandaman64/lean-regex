import Batteries.Data.String
import Mathlib.Tactic.Common
import Regex.Data.String

namespace String.Pos

theorem valid_of_isValidAux (cs : List Char) (p i : Pos) (h : isValid.go p cs i) :
  ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ p = i + ⟨utf8Len cs₁⟩ := by
  induction cs generalizing i with
  | nil =>
    simp [isValid.go] at h
    exact ⟨[], [], rfl, by simp [h, Pos.ext_iff]⟩
  | cons c cs ih =>
    simp [isValid.go] at h
    cases h with
    | inl eq => exact ⟨[], c :: cs, rfl, by simp [eq, Pos.ext_iff]⟩
    | inr h =>
      have ⟨cs₁, cs₂, eqs, eq⟩ := ih (i + c) h
      exact ⟨c :: cs₁, cs₂, by simp [eqs], by simp [eq, Pos.ext_iff]; omega⟩

theorem valid_of_isValid {s : String} {p : Pos} (v : p.isValid s) : p.Valid s := by
  unfold isValid at v
  have ⟨cs₁, cs₂, eqs, eq⟩ := valid_of_isValidAux s.data p 0 v
  simp [Pos.ext_iff] at eq
  have v := Valid.mk cs₁ cs₂
  simpa [←eqs, ←eq] using v

theorem isValid_of_validAux (cs₁ cs₂ : List Char) (p i : Pos) (hp : p = i + ⟨utf8Len cs₁⟩) :
  isValid.go p (cs₁ ++ cs₂) i :=
  match cs₁, cs₂ with
  | [], [] => by
    simp [Pos.ext_iff] at hp
    simp [isValid.go, Pos.ext_iff, hp]
  | [], c :: cs₂ => by
    simp [Pos.ext_iff] at hp
    simp [isValid.go, Pos.ext_iff, hp]
  | c :: cs₁, cs₂ => by
    simp [isValid.go]
    exact .inr (isValid_of_validAux cs₁ cs₂ p (i + c) (by simp [Pos.ext_iff, hp]; omega))

theorem isValid_of_valid (cs₁ cs₂ : List Char) (p : Pos) (hp : p = ⟨utf8Len cs₁⟩) : isValid ⟨cs₁ ++ cs₂⟩ p :=
  isValid_of_validAux cs₁ cs₂ p 0 (by simp [Pos.ext_iff, hp])

end String.Pos

namespace String.Iterator

theorem ext {it₁ it₂ : Iterator} (hs : it₁.s = it₂.s) (hi : it₁.i = it₂.i) : it₁ = it₂ :=
  show ⟨it₁.s, it₁.i⟩ = it₂ from hs ▸ hi ▸ rfl

theorem ext_iff {it₁ it₂ : Iterator} : it₁ = it₂ ↔ it₁.s = it₂.s ∧ it₁.i = it₂.i :=
  ⟨fun h => ⟨h ▸ rfl, h ▸ rfl⟩, fun ⟨hs, hi⟩ => ext hs hi⟩

theorem hasNext_of_not_atEnd {it : Iterator} (h : ¬it.atEnd) : it.hasNext := by
  simp [hasNext, atEnd] at *
  exact h

@[simp]
theorem ne_next (it : Iterator) : it ≠ it.next := by
  simp [ext_iff, next, Pos.ext_iff]
  exact Nat.ne_of_lt (lt_next it)

@[simp]
theorem next_ne (it : Iterator) : it.next ≠ it := it.ne_next.symm

theorem nextn_next_eq_next_nextn (it : Iterator) (n : Nat) : (it.nextn n).next = it.next.nextn n := by
  induction n generalizing it with
  | zero => simp [nextn]
  | succ n ih => simp [nextn, ih it.next]

end String.Iterator

namespace String.Iterator.Valid

theorem next' {it : Iterator} (v : it.Valid) (h : ¬it.atEnd) : it.next.Valid := by
  apply v.next
  simp [hasNext, atEnd] at *
  exact h

theorem of_isValid {it : Iterator} (v : it.pos.isValid it.toString) : it.Valid := it.pos.valid_of_isValid v

theorem isValid {it : Iterator} (v : it.Valid) : it.pos.isValid it.toString := by
  have ⟨l, r, vf⟩ := v.validFor
  have eqs : it.toString = ⟨l.reverse ++ r⟩ := by
    simp [Iterator.toString, vf.toString]
  have := it.pos.isValid_of_valid l.reverse r (by simp [vf.pos])
  exact eqs ▸ this

end String.Iterator.Valid

namespace String

theorem eq_of_append_utf8Len {cs₁ cs₂ cs₃ cs₄ : List Char}
  (h₁ : cs₁ ++ cs₂ = cs₃ ++ cs₄) (h₂ : utf8Len cs₁ = utf8Len cs₃) :
  cs₁ = cs₃ ∧ cs₂ = cs₄ := by
  induction cs₁ generalizing cs₃ with
  | nil =>
    have := String.utf8Len_eq_zero.mp h₂.symm
    simp_all
  | cons c cs₁' ih =>
    cases cs₃ with
    | nil =>
      simp at h₂
      have := Char.utf8Size_pos c
      omega
    | cons c' cs₃' =>
      simp at h₁
      simp [h₁] at h₂
      have := ih h₁.2 h₂
      simp [h₁, this]

end String

namespace String.Iterator.ValidFor

theorem eq {it : Iterator} {l₁ r₁ l₂ r₂} (v₁ : it.ValidFor l₁ r₁) (v₂ : it.ValidFor l₂ r₂) :
  l₁ = l₂ ∧ r₁ = r₂ := by
  have o₁ := v₁.out'
  have o₂ := v₂.out'
  simp [o₁, String.ext_iff, Pos.ext_iff] at o₂
  have := String.eq_of_append_utf8Len o₂.1 (by simp [o₂.2])
  simp at this
  exact this

theorem eq_it {it₁ it₂ : Iterator} {l r} (v₁ : it₁.ValidFor l r) (v₂ : it₂.ValidFor l r) : it₁ = it₂ := by
  simp [Iterator.ext_iff, v₁.toString, v₂.toString, v₁.pos, v₂.pos]

theorem exists_cons_of_not_atEnd {it : Iterator} (v : it.ValidFor l r) (h : ¬it.atEnd) :
  ∃ r', r = it.curr :: r' := by
  have := v.atEnd
  simp [h] at this
  have ⟨c, r', heq⟩ := List.exists_cons_of_ne_nil this
  subst heq
  have := v.curr
  simp at this
  subst this
  exact ⟨r', rfl⟩

end String.Iterator.ValidFor

namespace String.Pos

/--
A variant of `Valid` that allows past-one position that represents the position after running
a search at the end of the string.
-/
def ValidPlus (s : String) (p : Pos) :=
  p.Valid s ∨ p = s.endPos + ⟨1⟩

theorem Valid.validPlus {s : String} {p : Pos} : p.Valid s → p.ValidPlus s := .inl

theorem next_endPos {s : String} : (s.next s.endPos) = s.endPos + ⟨1⟩ := by
  have next_eq := next_of_valid' s.data []
  simp [Char.utf8Size] at next_eq
  -- definitionally equal to the goal now.
  exact next_eq

theorem validPlus_of_next_valid {s : String} {p : Pos} (h : p.Valid s) : (s.next p).ValidPlus s := by
  have : p ≤ s.endPos := Valid.le_endPos h
  cases Nat.lt_or_eq_of_le this with
  | inl lt => exact .inl (valid_next h lt)
  | inr eq =>
    have : p = s.endPos := ext eq
    subst p
    exact .inr next_endPos

theorem ValidPlus.valid_of_le {s : String} {p : Pos} (le : p ≤ s.endPos) (vp : p.ValidPlus s) : p.Valid s := by
  cases vp with
  | inl v => exact v
  | inr eq =>
    subst eq
    have : s.endPos.byteIdx + 1 ≤ s.endPos.byteIdx := le
    omega

end String.Pos
