
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

theorem char_mem_caseFoldEquivTable (c : Char) : c.val ∈ caseFoldEquivTable[(Internal.getCaseFoldChar_spec c).val]! := by
  unfold caseFoldEquivTable caseFoldEquivTableThunk
  dsimp [Thunk.get, Thunk.mk]
  have h_mem_table := getCaseFoldChar_pair_mem_table c
  obtain ⟨arr, h_some, h_mem⟩ := buildCaseFoldEquivTable_complete c.val (Internal.getCaseFoldChar_spec c).val h_mem_table
  simp only [Std.HashMap.getElem!_eq_get!_getElem?, h_some, Option.get!_some]
  exact h_mem

theorem buildCaseFoldEquivTable_soundness (u tgt : UInt32) :
    (∃ arr, buildCaseFoldEquivTable[tgt]? = some arr ∧ u ∈ arr) →
    ((u, tgt) ∈ caseFoldTable.toList ∨ u = tgt) := by
  dsimp [buildCaseFoldEquivTable]
  apply caseFold_soundness caseFoldTable.toList {} u tgt
  intro k
  exact Std.HashMap.getElem?_empty

theorem caseFoldEquivTable_mem_cases (u : UInt32) (tgt : Char)
    (h_mem : u ∈ caseFoldEquivTable[tgt.val]!) :
    (u, tgt.val) ∈ caseFoldTable.toList ∨ u = tgt.val := by
  simp only [caseFoldEquivTable, caseFoldEquivTableThunk, Thunk.get,
             Std.HashMap.getElem!_eq_get!_getElem?] at h_mem
  cases h_lookup : buildCaseFoldEquivTable[tgt.val]? with
  | none =>
    simp only [h_lookup, Option.get!_none] at h_mem
    exact (Array.not_mem_empty u h_mem).elim
  | some arr =>
    simp only [h_lookup, Option.get!_some] at h_mem
    exact buildCaseFoldEquivTable_soundness u tgt.val ⟨arr, h_lookup, h_mem⟩

theorem caseFoldTable_sound (u : UInt32) (tgt : Char) :
    u ∈ caseFoldEquivTable[tgt.val]! → Internal.getCaseFoldChar_spec (Char.ofNat u.toNat) = tgt := by
  intro h_mem
  have h_tgt_eq : Char.ofNat tgt.val.toNat = tgt := Char.ofNat_toNat tgt
  cases caseFoldEquivTable_mem_cases u tgt h_mem with
  | inl h_in_table =>
    rw [getCaseFoldChar_eq_of_mem u tgt.val h_in_table, h_tgt_eq]
  | inr h_u_eq_tgt =>
    subst h_u_eq_tgt
    have h_exists_src : ∃ src, (src, tgt.val) ∈ caseFoldTable.toList := by
      simp only [caseFoldEquivTable, caseFoldEquivTableThunk, Thunk.get,
                 Std.HashMap.getElem!_eq_get!_getElem?] at h_mem
      cases h_lookup : buildCaseFoldEquivTable[tgt.val]? with
      | none =>
        simp only [h_lookup, Option.get!_none] at h_mem
        exact (Array.not_mem_empty tgt.val h_mem).elim
      | some _ =>
        exact buildCaseFoldEquivTable_key_exists tgt.val (by simp [h_lookup])
    rw [getCaseFoldChar_fixed_of_is_target tgt.val h_exists_src, h_tgt_eq]

theorem caseFoldEquivTable_valid (u : UInt32) (tgt : Char) :
    u ∈ caseFoldEquivTable[tgt.val]! → UInt32.isValidChar u := by
  intro h_mem
  cases caseFoldEquivTable_mem_cases u tgt h_mem with
  | inl h_in_table =>
    have h_in_array : (u, tgt.val) ∈ caseFoldTable := Array.mem_toList_iff.mp h_in_table
    obtain ⟨i, hi, h_entry⟩ := Array.mem_iff_getElem.mp h_in_array
    have h_i_bang : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
    have h_src_eq : (caseFoldTable[i]!).1 = u := by rw [h_i_bang, h_entry]
    rw [← h_src_eq]
    exact caseFoldTable_src_valid i hi
  | inr h_u_eq_tgt =>
    rw [h_u_eq_tgt]
    exact tgt.valid

theorem mem_getCaseFoldEquivChars_iff {c₁ c₂ : Char} :
    c₂ ∈ Internal.getCaseFoldEquivChars_spec c₁ ↔ c₂.val ∈ caseFoldEquivTable[(Internal.getCaseFoldChar_spec c₁).val]! := by
  simp only [Internal.getCaseFoldEquivChars_spec, Array.mem_map]
  constructor
  · rintro ⟨u, h_mem, rfl⟩
    have h_valid := caseFoldEquivTable_valid u (Internal.getCaseFoldChar_spec c₁) h_mem
    simp only [Char.ofNat, dif_pos h_valid]
    exact h_mem
  · intro h_mem
    exact ⟨c₂.val, h_mem, Char.ofNat_toNat c₂⟩

theorem CaseFoldEquiv_iff_CaseFoldEquiv' {c₁ c₂ : Char} : CaseFoldEquiv c₁ c₂ ↔ CaseFoldEquiv' c₁ c₂ := by
  simp only [CaseFoldEquiv, CaseFoldEquiv']
  have h_c₂_id : Char.ofNat c₂.val.toNat = c₂ := Char.ofNat_toNat c₂
  constructor
  · intro h
    rw [mem_getCaseFoldEquivChars_iff] at h
    have h_sound := caseFoldTable_sound c₂.val (Internal.getCaseFoldChar_spec c₁) h
    rw [h_c₂_id] at h_sound
    exact h_sound.symm
  · intro h
    rw [mem_getCaseFoldEquivChars_iff, h]
    exact char_mem_caseFoldEquivTable c₂

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
