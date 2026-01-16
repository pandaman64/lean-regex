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
      exact ⟨old_arr, h_mem, fun x hx => hx⟩
  next h_not_found =>
    by_cases h_k : k = tgt
    · subst h_k
      simp_all
    · rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm h_k]
      exact ⟨old_arr, h_mem, fun x hx => hx⟩

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
    (s t : UInt32)
    (h_in_list : (s, t) ∈ pairs) :
    let final := pairs.foldl insertCaseFoldEquiv init
    ∃ arr, final[t]? = some arr ∧ s ∈ arr := by
  induction pairs generalizing init with
  | nil => contradiction
  | cons pair tail ih =>
    simp only [List.foldl_cons]
    cases h_in_list with
    | head _ =>
      exact foldl_insertCaseFoldEquiv_preserves tail _ t s (insertCaseFoldEquiv_src_mem init s t)
    | tail _ h_tail =>
      exact ih (insertCaseFoldEquiv init pair) h_tail

theorem buildCaseFoldEquivTable_correct (s t : UInt32) :
    (s, t) ∈ caseFoldTable.toList →
    ∃ arr, buildCaseFoldEquivTable[t]? = some arr ∧ s ∈ arr :=
  fun h => caseFold_in_result caseFoldTable.toList {} s t h

theorem insertCaseFoldEquiv_mem_reverse
    (m : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32)
    (k : UInt32) (x : UInt32)
    (arr : Array UInt32) :
    let new_map := insertCaseFoldEquiv m (src, tgt)
    new_map[k]? = some arr → x ∈ arr →
    (k = tgt ∧ (x = src ∨ x = tgt)) ∨ (∃ old, m[k]? = some old ∧ x ∈ old) := by
  dsimp [insertCaseFoldEquiv]
  split <;> rename_i old_or_h
  all_goals by_cases h_k : k = tgt
  · subst h_k
    rw [Std.HashMap.getElem?_insert_self]; simp
    intro h_eq h_mem; subst h_eq
    simp at h_mem
    cases h_mem with
    | inl h_in => exact Or.inr ⟨_, old_or_h, h_in⟩
    | inr h_eq => apply Or.inl; exact Or.symm (Or.inr h_eq)
  · rw [Std.HashMap.getElem?_insert]; simp [Ne.symm h_k]
    intro h_some h_mem
    exact Or.inr ⟨arr, h_some, h_mem⟩
  · subst h_k
    rw [Std.HashMap.getElem?_insert_self]; simp
    intro h_eq h_mem; subst h_eq
    simp at h_mem
    apply Or.inl
    exact Or.symm h_mem
  · rw [Std.HashMap.getElem?_insert];
    simp [Ne.symm h_k]
    intro h_some h_mem
    exact Or.inr ⟨arr, h_some, h_mem⟩

theorem caseFold_soundness
    (pairs : List (UInt32 × UInt32))
    (init : Std.HashMap UInt32 (Array UInt32))
    (u tgt : UInt32)
    (h_init_empty : ∀ (k : UInt32), init[k]? = none) :
    (∃ arr, (pairs.foldl insertCaseFoldEquiv init)[tgt]? = some arr ∧ u ∈ arr) →
    ((u, tgt) ∈ pairs ∨ u = tgt) := by
  intro h_found
  suffices H_gen : ∀ (m : Std.HashMap UInt32 (Array UInt32)),
      (∃ arr, (pairs.foldl insertCaseFoldEquiv m)[tgt]? = some arr ∧ u ∈ arr) →
      ((u, tgt) ∈ pairs ∨ u = tgt ∨ ∃ old, m[tgt]? = some old ∧ u ∈ old) by
    specialize H_gen init h_found
    rcases H_gen with h_in_list | h_eq | ⟨old, h_some, _⟩
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
    rcases ih with h_in_tail | h_u_eq_tgt | ⟨old, h_some_old, h_mem_old⟩
    · left
      apply List.mem_cons_of_mem
      exact h_in_tail
    · right; left
      exact h_u_eq_tgt
    · have h_rev := insertCaseFoldEquiv_mem_reverse m src key tgt u old h_some_old h_mem_old
      rcases h_rev with ⟨rfl, (rfl | rfl)⟩ | h_in_prev_m
      · grind
      · right; left
        rfl
      · right; right
        exact h_in_prev_m

theorem insertCaseFoldEquiv_key_is_tgt
    (m : Std.HashMap UInt32 (Array UInt32))
    (src tgt : UInt32)
    (k : UInt32) :
    let new_map := insertCaseFoldEquiv m (src, tgt)
    new_map[k]? ≠ none → m[k]? ≠ none ∨ k = tgt := by
  dsimp [insertCaseFoldEquiv]
  split
  next old_arr h_found =>
    by_cases h_eq : k = tgt
    · intro _; right; exact h_eq
    · rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm h_eq]
      intro h; left; exact h
  next h_not_found =>
    by_cases h_eq : k = tgt
    · intro _; right; exact h_eq
    · rw [Std.HashMap.getElem?_insert]
      simp [Ne.symm h_eq]
      intro h; left; exact h

theorem buildCaseFoldEquivTable_key_exists (k : UInt32) :
    buildCaseFoldEquivTable[k]? ≠ none →
    ∃ src, (src, k) ∈ caseFoldTable.toList := by
  dsimp [buildCaseFoldEquivTable]
  suffices H : ∀ (m : Std.HashMap UInt32 (Array UInt32)),
      (caseFoldTable.toList.foldl insertCaseFoldEquiv m)[k]? ≠ none →
      m[k]? ≠ none ∨ (∃ src, (src, k) ∈ caseFoldTable.toList) by
    intro h
    have := H {} h
    cases this with
    | inl h_empty =>
      simp at h_empty
    | inr h_exists =>
      exact h_exists
  intro m
  induction caseFoldTable.toList generalizing m with
  | nil =>
    intro h
    left; exact h
  | cons pair tail ih =>
    simp only [List.foldl_cons]
    intro h
    rcases pair with ⟨src, tgt⟩
    specialize ih (insertCaseFoldEquiv m (src, tgt)) h
    cases ih with
    | inl h_prev =>
      have h_key := insertCaseFoldEquiv_key_is_tgt m src tgt k h_prev
      cases h_key with
      | inl h_m => left; exact h_m
      | inr h_eq =>
        right
        exists src
        subst h_eq
        apply List.mem_cons_self
    | inr h_exists =>
      right
      obtain ⟨s, h_mem⟩ := h_exists
      exists s
      exact List.mem_cons_of_mem _ h_mem

end Regex.Unicode
