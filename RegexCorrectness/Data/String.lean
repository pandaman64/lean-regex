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
  unfold expand
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

namespace String.Iterator.Valid

theorem next' {it : Iterator} (v : it.Valid) (h : ¬it.atEnd) : it.next.Valid := by
  apply v.next
  simp [hasNext, atEnd] at *
  exact h

end String.Iterator.Valid

namespace String.Iterator.ValidFor

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
