import Batteries.Data.String
import Mathlib.Tactic.Common
/--
Increment the end position by one character.
-/
def Substring.expand (s : Substring) : Substring :=
  if s.stopPos < s.str.endPos then
    { s with stopPos := s.str.next s.stopPos }
  else
    s

namespace Substring.ValidFor

theorem expand (v : ValidFor l m (c :: r) s) : ValidFor l (m ++ [c]) r s.expand := by
  have : s.stopPos < s.str.endPos := by
    simp [v.stopPos, v.str]
    have : 0 < c.utf8Size := Char.utf8Size_pos c
    omega
  unfold Substring.expand
  simp [this]
  simp [v.stopPos, v.str, String.next]
  have : String.get ⟨l ++ (m ++ c :: r)⟩ ⟨String.utf8Len l + String.utf8Len m⟩ = c := by
    have eq₁ : l ++ (m ++ c :: r) = (l ++ m) ++ (c :: r) := by simp
    have eq₂ : String.utf8Len l + String.utf8Len m = String.utf8Len (l ++ m) := by simp
    rw [eq₁, eq₂, String.get_of_valid]
    simp
  rw [this]

  apply of_eq
  . simp
  . simp [v.startPos]
  . simp [Nat.add_assoc]

end Substring.ValidFor

namespace String.Iterator

theorem ext {it₁ it₂ : Iterator} (hs : it₁.s = it₂.s) (hi : it₁.i = it₂.i) : it₁ = it₂ :=
  show ⟨it₁.s, it₁.i⟩ = it₂ from hs ▸ hi ▸ rfl

theorem ext_iff {it₁ it₂ : Iterator} : it₁ = it₂ ↔ it₁.s = it₂.s ∧ it₁.i = it₂.i :=
  ⟨fun h => ⟨h ▸ rfl, h ▸ rfl⟩, fun ⟨hs, hi⟩ => ext hs hi⟩

theorem hasNext_of_not_atEnd {it : Iterator} (h : ¬it.atEnd) : it.hasNext := by
  simp [hasNext, atEnd] at *
  exact h

end String.Iterator

namespace String.Iterator.Valid

theorem next' {it : Iterator} (v : it.Valid) (h : ¬it.atEnd) : it.next.Valid := by
  apply v.next
  simp [hasNext, atEnd] at *
  exact h

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
