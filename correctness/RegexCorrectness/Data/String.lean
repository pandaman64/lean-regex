import Batteries.Data.String
import Mathlib.Tactic.Common
import Regex.Data.String

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

namespace String.ValidPos

theorem find_le_pos {s : String} {pos : ValidPos s} {p : Char → Bool} : pos ≤ pos.find p := by
  fun_induction find
  next => exact le_refl _
  next => exact le_refl _
  next ih => exact le_trans (le_of_lt (lt_next _)) ih

theorem find_soundness {s : String} {pos : ValidPos s} {p : Char → Bool} :
  (∃ h : pos.find p ≠ s.endValidPos, p ((pos.find p).get h)) ∨ pos.find p = s.endValidPos := by
  fun_induction find <;> grind

theorem find_completenessAux {s : String} {pos : ValidPos s} (p : Char → Bool) {l mr : String} (sp : pos.Splits l mr) :
  ∃ m r, (pos.find p).Splits (l ++ m) r ∧ ∀ c, m.contains c → ¬p c := by
  fun_induction find generalizing l mr
  next =>
    simp only [splits_endValidPos_iff] at sp
    exact ⟨"", "", by simp [sp], by simp [String.contains_iff]⟩
  next => exact ⟨"", mr, by simpa using sp, by simp [String.contains_iff]⟩
  next pos ne h ih =>
    obtain ⟨mr', eq⟩ := sp.exists_eq_singleton_append ne
    subst eq
    obtain ⟨m, r, sp', h'⟩ := ih sp.next
    exact ⟨singleton (pos.get ne) ++ m, r, String.append_assoc ▸ sp', by simp_all [String.contains_iff]⟩

theorem find_completeness {s : String} {pos pos' : ValidPos s} {p : Char → Bool}
  (ge : pos ≤ pos') (lt : pos' < pos.find p) :
  ¬p (pos'.get (ne_endValidPos_of_lt lt)) := by
  obtain ⟨m, r, sp, h⟩ := find_completenessAux p pos.splits
  obtain ⟨l₁, l₂, eq, sp'⟩ := sp.exists_eq_append_left_of_lt lt
  have : l₁.utf8ByteSize = pos'.offset.byteIdx := by
    simp [←String.byteIdx_rawEndPos, sp'.offset_eq_rawEndPos]
  obtain ⟨m', rfl, rfl⟩ := String.eq_of_append_eq (by simpa [this] using ge) eq
  match String.empty_or_eq_singleton_append l₂ with
  | .inl eq' =>
    simp [eq'] at sp sp'
    have eq'' : pos' = pos.find p := ValidPos.ext (sp.offset_eq_rawEndPos ▸ sp'.offset_eq_rawEndPos)
    exact (Nat.lt_irrefl _ (eq'' ▸ lt)).elim
  | .inr ⟨c, l₂', eq'⟩ =>
    simp only [eq', append_assoc] at sp'
    have get_eq := splits_get_singleton sp'
    apply h
    simp [eq', get_eq, String.contains_iff]

end String.ValidPos
