import Regex.NFA.VM.Basic

theorem Array.isEmpty_iff {α} {a : Array α} : a.isEmpty ↔ a = #[] := by
  simp [Array.isEmpty]
  apply Iff.intro
  . exact eq_empty_of_size_eq_zero
  . intro h
    simp [h]

theorem Array.mem_back' {a : Array α} (hemp : ¬ a.isEmpty) : a.back' hemp ∈ a := by
  simp [back', Array.mem_def, Array.getElem_eq_data_get]
  apply List.get_mem

theorem Array.mem_push (a : Array α) (x y : α) :
  y ∈ a.push x ↔ y ∈ a ∨ y = x := by
  unfold Array.push
  simp [Array.mem_def]

@[simp]
theorem Array.mem_of_push (a : Array α) (x : α) :
  x ∈ a.push x := by
  simp [Array.mem_def]

theorem Array.push_pop_eq (a : Array α) (hemp : ¬ a.isEmpty) :
  a.pop.push (a.back' hemp) = a := by
  simp at hemp
  have : 0 < a.size := Nat.pos_of_ne_zero hemp
  apply Array.ext
  . simp [Nat.sub_add_cancel this]
  . simp [Nat.sub_add_cancel this]
    intro i h _
    rw [Array.get_push]
    split
    case inl h' => rw [Array.getElem_pop]
    case inr h' =>
      simp at h'
      have : i + 1 - 1 ≤ a.size - 1 := Nat.sub_le_sub_right h _
      simp at this
      have : i = a.size - 1 := Nat.le_antisymm this h'
      simp [back', this]

theorem Array.mem_pop (a : Array α) (x : α) (hemp : ¬ a.isEmpty)
  (mem : x ∈ a) (neq : x ≠ a.back' hemp) : x ∈ a.pop := by
  rw [←Array.push_pop_eq a hemp] at mem
  cases (Array.mem_push _ _ _).mp mem with
  | inl mem => exact mem
  | inr eq => exact absurd eq neq

theorem Array.mem_pop_or_eq_of_mem (a : Array α) (x : α) (hemp : ¬ a.isEmpty)
  (mem : x ∈ a) : x ∈ a.pop ∨ x = a.back' hemp := by
  rw [←Array.push_pop_eq a hemp] at mem
  exact (Array.mem_push _ _ _).mp mem

theorem Array.mem_of_mem_pop (a : Array α) (x : α) (mem : x ∈ a.pop) :
  x ∈ a := by
  cases decEq a.isEmpty true with
  | isTrue hemp =>
    have := (Array.isEmpty_iff).mp hemp
    subst this
    simp at mem
  | isFalse hemp =>
    rw [←Array.push_pop_eq a hemp]
    apply (Array.mem_push _ _ _).mpr
    exact Or.inl mem
