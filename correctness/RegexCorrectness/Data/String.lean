import Batteries.Data.String
import Mathlib.Tactic.Common
import Regex.Data.String

open String (Pos)

theorem List.eq_of_append_eq (s₁ s₂ t₁ t₂ : List Char) (le : String.utf8Len s₁ ≤ String.utf8Len t₁) (eq : s₁ ++ s₂ = t₁ ++ t₂) :
  ∃ u, s₁ ++ u = t₁ ∧ s₂ = u ++ t₂ := by
  induction s₁ generalizing t₁ with
  | nil => simp_all
  | cons c s₁ ih =>
    match t₁ with
    | [] => grind [String.utf8Len, Char.utf8Size_pos]
    | c' :: t₁ =>
      simp only [cons_append, cons.injEq] at eq
      simp only [eq, String.utf8Len_cons, Nat.add_le_add_iff_right] at le
      obtain ⟨u, eq₁, eq₂⟩ := ih t₁ le eq.2
      exact ⟨u, by simp [eq, eq₁], eq₂⟩

theorem String.eq_of_append_eq {s₁ s₂ t₁ t₂ : String} (le : s₁.utf8ByteSize ≤ t₁.utf8ByteSize) (eq : s₁ ++ s₂ = t₁ ++ t₂) :
  ∃ u, s₁ ++ u = t₁ ∧ s₂ = u ++ t₂ := by
  have ⟨u, eq₁, eq₂⟩ := List.eq_of_append_eq s₁.toList s₂.toList t₁.toList t₂.toList
    (by simpa [String.utf8Len_toList] using le) (by simp [←String.toList_append, eq])
  have eq₁' : (String.ofList s₁.toList) ++ (String.ofList u) = String.ofList t₁.toList := by
    rw [←String.ofList_append, eq₁]
  have eq₂' : (String.ofList s₂.toList) = (String.ofList u) ++ (String.ofList t₂.toList) := by
    rw [←String.ofList_append, eq₂]
  exact ⟨String.ofList u, by simpa using eq₁', by simpa using eq₂'⟩

theorem String.empty_or_eq_singleton_append (s : String) :
  s = "" ∨ ∃ c t, s = singleton c ++ t := by
  obtain ⟨cs, rfl⟩ := String.exists_eq_ofList s
  match cs with
  | [] => exact .inl rfl
  | c :: cs => exact .inr ⟨c, String.ofList cs, by simp [String.singleton_eq_ofList, ←String.ofList_append]⟩

namespace Regex.Data.String

theorem find_le_pos {s : String} {pos : Pos s} {p : Char → Bool} : pos ≤ find pos p := by
  fun_induction find
  next => exact Pos.le_refl _
  next => exact Pos.le_refl _
  next pos ne h ih => exact Pos.le_trans (Pos.le_of_lt pos.lt_next) ih

theorem find_soundness {s : String} {pos : Pos s} {p : Char → Bool} :
  (∃ h : find pos p ≠ s.endPos, p ((find pos p).get h)) ∨ find pos p = s.endPos := by
  fun_induction find <;> grind

theorem find_completeness {s : String} {pos pos' : Pos s} {p : Char → Bool}
  (ge : pos ≤ pos') (lt : pos' < find pos p) :
  ¬p (pos'.get (Pos.ne_endPos_of_lt lt)) := by
  fun_induction find --generalizing pos'
  next => grind
  next pos ne h => grind
  next pos ne h ih =>
    have : pos = pos' ∨ pos.next ne ≤ pos' := by grind only [Pos.next_le_of_lt]
    grind

end Regex.Data.String
