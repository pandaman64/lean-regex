
import Regex.Unicode.CaseFold
import Std.Data.HashMap
import Mathlib.Data.List.Basic
import RegexCorrectness.Unicode.CaseFold
import RegexCorrectness.Unicode.CaseFoldBinarySearch

set_option autoImplicit false

open Regex.Unicode

namespace Regex.Unicode

/-- Two characters are case-fold equivalent if one is in the case-fold equivalence class of the other. -/
def CaseFoldEquiv (c₁ c₂ : Char) : Prop :=
  c₂ ∈ Internal.getCaseFoldEquivChars_spec c₁

def CaseFoldEquiv' (c₁ c₂ : Char) : Prop :=
  Internal.getCaseFoldChar_spec c₁ = Internal.getCaseFoldChar_spec c₂

theorem buildCaseFoldEquivTable_soundness (u tgt : UInt32) :
    (∃ arr, buildCaseFoldEquivTable[tgt]? = some arr ∧ u ∈ arr) →
    ((u, tgt) ∈ caseFoldTable.toList ∨ u = tgt) := by
  dsimp [buildCaseFoldEquivTable]
  apply caseFold_soundness caseFoldTable.toList {} u tgt
  intro k
  exact Std.HashMap.getElem?_empty

theorem getCaseFoldChar_spec_idempotent (c : Char) :
    Internal.getCaseFoldChar_spec (Internal.getCaseFoldChar_spec c) = Internal.getCaseFoldChar_spec c := by
  let c' := Internal.getCaseFoldChar_spec c
  if h : c' = c then
    have h_eq : Internal.getCaseFoldChar_spec c = c := h
    rw [h_eq]
    exact Char.ext (congrArg Char.val h)
  else
    have h_in := getCaseFoldChar_spec_ne_implies_in_table c c' rfl (Ne.symm h)
    have h_exists : ∃ src, (src, c'.val) ∈ caseFoldTable.toList :=
      ⟨c.val, h_in⟩
    have h_res := getCaseFoldChar_fixed_of_is_target c'.val h_exists
    have h_char_eq : Char.ofNat c'.val.toNat = c' := by
      simp [Char.ofNat]
      simp [c'.valid]
      exact Char.ext rfl
    rw [h_char_eq] at h_res
    exact h_res

theorem caseFoldEquivTable_mem_self
    (k : UInt32) (arr : Array UInt32) :
    caseFoldEquivTable[k]? = some arr → k ∈ arr := by
  rw [caseFoldEquivTable, caseFoldEquivTableThunk, Thunk.get, buildCaseFoldEquivTable]
  generalize caseFoldTable.toList = l
  suffices ∀ (m : Std.HashMap UInt32 (Array UInt32)),
    (∀ (k' : UInt32) (arr' : Array UInt32), m[k']? = some arr' → k' ∈ arr') →
    let res := l.foldl insertCaseFoldEquiv m
    res[k]? = some arr → k ∈ arr by
    apply this {} (fun _ _ h => by simp at h)
  intro m h_inv
  induction l generalizing m with
  | nil =>
    exact h_inv k arr
  | cons pair tail ih =>
    simp only [List.foldl_cons]
    apply ih
    intro k' arr' h_get
    rcases pair with ⟨src, tgt⟩
    dsimp [insertCaseFoldEquiv] at h_get
    split at h_get <;> rename_i existing_arr h_found
    · by_cases h_kt : k' = tgt
      · subst h_kt
        rw [Std.HashMap.getElem?_insert_self] at h_get
        injection h_get with h_eq
        subst h_eq
        rw [Array.mem_push]
        left
        grind
      · rw [Std.HashMap.getElem?_insert] at h_get
        simp [Ne.symm h_kt] at h_get
        exact h_inv k' arr' h_get
    · by_cases h_kt : k' = tgt
      · subst h_kt
        rw [Std.HashMap.getElem?_insert_self] at h_get
        injection h_get with h_eq
        subst h_eq
        simp
      · rw [Std.HashMap.getElem?_insert] at h_get
        simp [Ne.symm h_kt] at h_get
        exact h_inv k' arr' h_get

theorem caseFoldEquivTable_none_imp_eq_fold
    (c : Char) (u : Char)
    (h_spec : Internal.getCaseFoldChar_spec c = u) :
    caseFoldEquivTable[u.val]? = none → c = u := by
  intro h_none
  by_contra h_ne
  have h_in := getCaseFoldChar_spec_ne_implies_in_table c u h_spec h_ne
  have ⟨arr, h_found, h_mem⟩ := buildCaseFoldEquivTable_complete c.val u.val h_in
  rw [caseFoldEquivTable, caseFoldEquivTableThunk, Thunk.get] at h_none
  rw [h_found] at h_none
  contradiction

theorem mem_getCaseFoldEquivChars_iff {c₁ c₂ : Char} :
    c₂ ∈ Internal.getCaseFoldEquivChars_spec c₁ ↔
    Internal.getCaseFoldChar_spec c₂ = Internal.getCaseFoldChar_spec c₁ := by
  dsimp [Internal.getCaseFoldEquivChars_spec]
  let u₁ := Internal.getCaseFoldChar_spec c₁
  let u₂ := Internal.getCaseFoldChar_spec c₂
  match h_map : caseFoldEquivTable[u₁.val]? with
  | some arr =>
    constructor
    · intro h_mem
      rw [Array.mem_map] at h_mem
      obtain ⟨u, h_u_in, h_u_eq⟩ := h_mem
      have h_sound := buildCaseFoldEquivTable_soundness u u₁.val ⟨arr, h_map, h_u_in⟩
      rcases h_sound with h_in_table | h_eq_val
      · have h_fold := getCaseFoldChar_eq_of_mem u u₁.val h_in_table
        rw [h_u_eq] at h_fold
        change _ = Char.ofNat u₁.toNat at h_fold
        rw [Char.ofNat_toNat] at h_fold
        exact h_fold
      · rw [h_eq_val] at h_u_eq
        change Char.ofNat u₁.toNat = c₂ at h_u_eq
        rw [Char.ofNat_toNat] at h_u_eq
        rw [← h_u_eq]
        exact getCaseFoldChar_spec_idempotent c₁
    · intro h_eq
      rw [Array.mem_map]
      exists c₂.val
      constructor
      · by_cases h_ne : c₂ ≠ u₁
        · have h_spec : Internal.getCaseFoldChar_spec c₂ = u₁ := h_eq
          have h_in_table := getCaseFoldChar_spec_ne_implies_in_table c₂ u₁ h_spec h_ne
          obtain ⟨arr', h_found, h_mem_arr⟩ := buildCaseFoldEquivTable_complete c₂.val u₁.val h_in_table
          rw [caseFoldEquivTable, caseFoldEquivTableThunk, Thunk.get] at h_map
          rw [h_found] at h_map
          injection h_map with h_arr_eq
          subst h_arr_eq
          exact h_mem_arr
        · simp only [not_not] at h_ne
          subst h_ne
          exact caseFoldEquivTable_mem_self u₁.val arr h_map
      · change Char.ofNat c₂.toNat = c₂
        exact Char.ofNat_toNat c₂
  | none =>
    have h_c1_eq_u1 : c₁ = u₁ := caseFoldEquivTable_none_imp_eq_fold c₁ u₁ rfl h_map
    constructor
    · intro h_mem
      simp only [Array.mem_singleton] at h_mem
      rw [h_mem, h_c1_eq_u1]
    · intro h_eq
      rw [h_c1_eq_u1] at h_eq
      have h_none_u2 : caseFoldEquivTable[u₂.val]? = none := by
        grind
      have h_c2_eq_u2 : c₂ = u₂ := caseFoldEquivTable_none_imp_eq_fold c₂ u₂ rfl h_none_u2
      rw [h_c2_eq_u2]
      grind

theorem CaseFoldEquiv_iff_CaseFoldEquiv' {c₁ c₂ : Char} : CaseFoldEquiv c₁ c₂ ↔ CaseFoldEquiv' c₁ c₂ := by
  simp only [CaseFoldEquiv, CaseFoldEquiv']
  rw [mem_getCaseFoldEquivChars_iff]
  tauto

scoped infix:50 " ≃ " => CaseFoldEquiv

theorem CaseFoldEquiv.refl (c : Char) : c ≃ c := by
  rw [CaseFoldEquiv_iff_CaseFoldEquiv']
  simp only [CaseFoldEquiv']

theorem CaseFoldEquiv.symm {c₁ c₂ : Char} (h : c₁ ≃ c₂) : c₂ ≃ c₁ := by
  rw [CaseFoldEquiv_iff_CaseFoldEquiv'] at h ⊢
  exact h.symm

theorem CaseFoldEquiv.trans {c₁ c₂ c₃ : Char} (h₁ : c₁ ≃ c₂) (h₂ : c₂ ≃ c₃) : c₁ ≃ c₃ := by
  rw [CaseFoldEquiv_iff_CaseFoldEquiv'] at h₁ h₂ ⊢
  exact h₁.trans h₂

theorem CaseFoldEquiv.equivalence : Equivalence CaseFoldEquiv :=
  ⟨CaseFoldEquiv.refl, CaseFoldEquiv.symm, CaseFoldEquiv.trans⟩

end Regex.Unicode
