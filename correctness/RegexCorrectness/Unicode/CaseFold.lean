import Regex.Unicode.CaseFold
import Std.Data.HashMap
import Mathlib.Data.List.Basic

set_option autoImplicit false

open Regex.Unicode

namespace Regex.Unicode

theorem insertCaseFoldEquiv_src_mem
    (result : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32) :
    let new_map := insertCaseFoldEquiv result (src, tgt)
    ∃ arr, new_map[tgt]? = some arr ∧ src ∈ arr := by
  dsimp [insertCaseFoldEquiv]
  split <;> simp

theorem insertCaseFoldEquiv_preserves_elements
    (result : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32)
    (k : UInt32) (old_arr : Array UInt32)
    (h_mem : result[k]? = some old_arr) :
    let new_map := insertCaseFoldEquiv result (src, tgt)
    ∃ new_arr, new_map[k]? = some new_arr ∧ ∀ x, x ∈ old_arr → x ∈ new_arr := by
  dsimp [insertCaseFoldEquiv]
  split
  next existing_arr h_found =>
    by_cases h_k : k = tgt
    · subst h_k
      rw [h_found] at h_mem
      injection h_mem with h_eq
      subst h_eq
      simp only [Std.HashMap.getElem?_insert_self]
      exact ⟨_, rfl, fun _ hx => by simp; exact Or.inl hx⟩
    · rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm h_k]
      exact ⟨old_arr, h_mem, fun _ hx => hx⟩
  next h_not_found =>
    by_cases h_k : k = tgt
    · simp_all
    · rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm h_k]
      exact ⟨old_arr, h_mem, fun _ hx => hx⟩

theorem foldl_insertCaseFoldEquiv_preserves
    (pairs : List (UInt32 × UInt32))
    (init : Std.HashMap UInt32 (Array UInt32))
    (k : UInt32) (val : UInt32)
    (h_pre : ∃ arr, init[k]? = some arr ∧ val ∈ arr) :
    let final := pairs.foldl insertCaseFoldEquiv init
    ∃ arr, final[k]? = some arr ∧ val ∈ arr := by
  induction pairs generalizing init with
  | nil => simp_all
  | cons pair tail ih =>
    simp only [List.foldl_cons]
    obtain ⟨old_arr, h_get, h_mem⟩ := h_pre
    obtain ⟨new_arr, h_new_get, h_subset⟩ :=
      insertCaseFoldEquiv_preserves_elements init pair.1 pair.2 k old_arr h_get
    exact ih _ ⟨new_arr, h_new_get, h_subset _ h_mem⟩

theorem caseFold_in_result
    (pairs : List (UInt32 × UInt32))
    (init : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32)
    (h_in_list : (src, tgt) ∈ pairs) :
    let final := pairs.foldl insertCaseFoldEquiv init
    ∃ arr, final[tgt]? = some arr ∧ src ∈ arr := by
  induction pairs generalizing init with
  | nil => contradiction
  | cons pair tail ih =>
    simp only [List.foldl_cons]
    cases h_in_list with
    | head _ =>
      exact foldl_insertCaseFoldEquiv_preserves tail _ tgt src
        (insertCaseFoldEquiv_src_mem init src tgt)
    | tail _ h_tail =>
      exact ih (insertCaseFoldEquiv init pair) h_tail

theorem buildCaseFoldEquivTable_complete (src tgt : UInt32) :
    (src, tgt) ∈ caseFoldTable.toList →
    ∃ arr, buildCaseFoldEquivTable[tgt]? = some arr ∧ src ∈ arr :=
  fun h => caseFold_in_result caseFoldTable.toList {} src tgt h

theorem mem_insertCaseFoldEquiv_implies
    (m : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32)
    (k : UInt32) (x : UInt32)
    (arr : Array UInt32) :
    let new_map := insertCaseFoldEquiv m (src, tgt)
    new_map[k]? = some arr → x ∈ arr →
    (k = tgt ∧ (x = src ∨ x = tgt)) ∨ (∃ old, m[k]? = some old ∧ x ∈ old) := by
  dsimp [insertCaseFoldEquiv]
  split
  next existing_arr h_found =>
    by_cases h_k : k = tgt
    · subst h_k
      rw [Std.HashMap.getElem?_insert_self]; simp
      intro h_eq h_mem; subst h_eq
      simp at h_mem
      cases h_mem with
      | inl h_in => exact Or.inr ⟨_, h_found, h_in⟩
      | inr h_eq => apply Or.inl; exact Or.symm (Or.inr h_eq)
    · rw [Std.HashMap.getElem?_insert]; simp [Ne.symm h_k]
      exact fun h_some h_mem => Or.inr ⟨arr, h_some, h_mem⟩
  next h_not_found =>
    by_cases h_k : k = tgt
    · subst h_k
      rw [Std.HashMap.getElem?_insert_self]; simp
      intro h_eq h_mem; subst h_eq
      simp at h_mem
      apply Or.inl
      exact Or.symm h_mem
    · rw [Std.HashMap.getElem?_insert]; simp [Ne.symm h_k]
      exact fun h_some h_mem => Or.inr ⟨arr, h_some, h_mem⟩

theorem caseFold_soundness
    (pairs : List (UInt32 × UInt32))
    (init : Std.HashMap UInt32 (Array UInt32))
    (elem tgt : UInt32)
    (h_init_empty : ∀ (k : UInt32), init[k]? = none) :
    (∃ arr, (pairs.foldl insertCaseFoldEquiv init)[tgt]? = some arr ∧ elem ∈ arr) →
    ((elem, tgt) ∈ pairs ∨ elem = tgt) := by
  intro h_found
  suffices h_gen : ∀ (m : Std.HashMap UInt32 (Array UInt32)),
      (∃ arr, (pairs.foldl insertCaseFoldEquiv m)[tgt]? = some arr ∧ elem ∈ arr) →
      ((elem, tgt) ∈ pairs ∨ elem = tgt ∨ ∃ old, m[tgt]? = some old ∧ elem ∈ old) by
    specialize h_gen init h_found
    rcases h_gen with h_in_list | h_eq | ⟨old, h_some, _⟩
    · left; exact h_in_list
    · right; exact h_eq
    · rw [h_init_empty tgt] at h_some
      contradiction
  clear h_found
  intro m
  induction pairs generalizing m with
  | nil => grind only [= List.foldl_nil]
  | cons pair tail ih =>
    intro h_in_result
    rcases pair with ⟨src, key⟩
    simp only [List.foldl_cons] at h_in_result
    let next_map := insertCaseFoldEquiv m (src, key)
    specialize ih next_map h_in_result
    rcases ih with h_in_tail | h_elem_eq_tgt | ⟨old, h_some_old, h_mem_old⟩
    · left
      apply List.mem_cons_of_mem
      exact h_in_tail
    · right; left
      exact h_elem_eq_tgt
    · have h_rev := mem_insertCaseFoldEquiv_implies m src key tgt elem old h_some_old h_mem_old
      rcases h_rev with ⟨rfl, (rfl | rfl)⟩ | h_in_prev_m
      · grind
      · right; left
        rfl
      · right; right
        exact h_in_prev_m

theorem insertCaseFoldEquiv_key_eq_tgt_of_new
    (m : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32)
    (k : UInt32) :
    let new_map := insertCaseFoldEquiv m (src, tgt)
    new_map[k]? ≠ none → m[k]? ≠ none ∨ k = tgt := by
  dsimp [insertCaseFoldEquiv]
  split <;> by_cases h_eq : k = tgt
  all_goals first
    | exact fun _ => Or.inr h_eq
    | rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm h_eq]
      exact fun h => Or.inl h

theorem buildCaseFoldEquivTable_key_exists (k : UInt32) :
    buildCaseFoldEquivTable[k]? ≠ none →
    ∃ src, (src, k) ∈ caseFoldTable.toList := by
  dsimp [buildCaseFoldEquivTable]
  suffices h_suffices : ∀ (m : Std.HashMap UInt32 (Array UInt32)),
      (caseFoldTable.toList.foldl insertCaseFoldEquiv m)[k]? ≠ none →
      m[k]? ≠ none ∨ (∃ src, (src, k) ∈ caseFoldTable.toList) by
    intro h
    rcases h_suffices {} h with h_empty | h_exists
    · simp at h_empty
    · exact h_exists
  intro m
  induction caseFoldTable.toList generalizing m with
  | nil => exact Or.inl
  | cons pair tail ih =>
    simp only [List.foldl_cons]
    intro h
    rcases pair with ⟨src, tgt⟩
    rcases ih (insertCaseFoldEquiv m (src, tgt)) h with h_prev | h_exists
    · rcases insertCaseFoldEquiv_key_eq_tgt_of_new m src tgt k h_prev with h_m | rfl
      · exact Or.inl h_m
      · exact Or.inr ⟨src, List.mem_cons_self ..⟩
    · obtain ⟨s, h_mem⟩ := h_exists
      exact Or.inr ⟨s, List.mem_cons_of_mem _ h_mem⟩

end Regex.Unicode
