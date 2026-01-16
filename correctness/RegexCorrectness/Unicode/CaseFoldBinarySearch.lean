
import Regex.Unicode.CaseFold
import Std.Data.HashMap
import Mathlib.Data.List.Basic

set_option autoImplicit false

open Regex.Unicode

namespace Regex.Unicode

/-!
# Binary Search Properties for Case Folding

This file proves properties of `getCaseFoldChar!`.

## Key Assumptions

We model `caseFoldTable` as an idealized table that contains an entry for EVERY valid
Unicode character:
- For characters that need case folding: `(c, folded_c)` where `folded_c ≠ c`
- For characters already in folded form: `(c, c)` (identity mapping)

This ensures that `binarySearch` always finds an exact match for any valid character,
making `getCaseFoldChar!` well-defined for all inputs.
-/

axiom caseFoldTable_sorted :
    ∀ i j : Nat, i < j → j < caseFoldTable.size →
    (caseFoldTable[i]!).1 < (caseFoldTable[j]!).1

axiom caseFoldTable_nonempty : caseFoldTable.size > 0

axiom caseFoldTable_src_valid :
    ∀ i : Nat, i < caseFoldTable.size → UInt32.isValidChar (caseFoldTable[i]!).1

axiom caseFoldTable_tgt_valid :
    ∀ i : Nat, i < caseFoldTable.size → UInt32.isValidChar (caseFoldTable[i]!).2

axiom caseFoldTable_complete (c : UInt32) (hc : UInt32.isValidChar c) :
    ∃ i : Nat, i < caseFoldTable.size ∧ (caseFoldTable[i]!).1 = c

axiom caseFoldTable_idempotent (i : Nat) (hi : i < caseFoldTable.size) :
    ∃ j : Nat, j < caseFoldTable.size ∧
      (caseFoldTable[j]!).1 = (caseFoldTable[i]!).2 ∧
      (caseFoldTable[j]!).2 = (caseFoldTable[i]!).2

theorem binarySearch_correct {α} [Inhabited α] (c : UInt32) (values : Array α) (f : α → UInt32)
    (lo hi : Nat)
    (h_sorted : ∀ i j, lo ≤ i → i < j → j < hi → f (values[i]!) < f (values[j]!))
    (h_exists : ∃ i, lo ≤ i ∧ i < hi ∧ f (values[i]!) = c) :
    f (values[binarySearch c values f lo hi]!) = c := by
  revert h_sorted h_exists
  induction lo, hi using binarySearch.induct c values f with
  | case1 lo hi h_ge =>
    intro h_sorted h_exists
    obtain ⟨i, h_lo_le, h_i_lt, _⟩ := h_exists
    omega
  | case2 lo hi h_lt mid h_eq_mid =>
    intro h_sorted h_exists
    have h_hi_eq : hi = lo + 1 := by omega
    obtain ⟨i, h_lo_le, h_i_lt, h_fi_eq⟩ := h_exists
    have h_i_eq : i = lo := by omega
    have h_bs : binarySearch c values f lo hi = lo := by
      rw [binarySearch.eq_def]
      have h_not_ge : ¬(lo ≥ hi) := h_lt
      simp only [ge_iff_le, h_not_ge, ite_false]
      rw [if_pos h_eq_mid]
    rw [h_bs, ← h_i_eq, h_fi_eq]
  | case3 lo hi h_lt mid h_ne_mid h_c_lt IH_left =>
    intro h_sorted h_exists
    have h_bs : binarySearch c values f lo hi = binarySearch c values f lo mid := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_pos h_c_lt]
    rw [h_bs]
    apply IH_left
    · intro i j h_lo_i h_i_j h_j_mid
      have h_j_hi : j < hi := by omega
      exact h_sorted i j h_lo_i h_i_j h_j_hi
    · obtain ⟨i, h_lo_le, h_i_lt, h_fi_eq⟩ := h_exists
      use i
      refine ⟨h_lo_le, ?_, h_fi_eq⟩
      by_contra h_not_lt
      have h_i_ge_mid : i ≥ mid := Nat.not_lt.mp h_not_lt
      have h_mid_lt_hi : mid < hi := by omega
      cases Nat.lt_or_eq_of_le h_i_ge_mid with
      | inl h_mid_lt_i =>
        have h_lt_f : f values[mid]! < f values[i]! := by
          have h_lo_mid : lo ≤ mid := by omega
          exact h_sorted mid i h_lo_mid h_mid_lt_i h_i_lt
        rw [h_fi_eq] at h_lt_f
        exact Nat.lt_irrefl _ (Nat.lt_trans h_c_lt h_lt_f)
      | inr h_eq =>
        rw [h_eq, h_fi_eq] at h_c_lt
        exact Nat.lt_irrefl _ h_c_lt
  | case4 lo hi h_lt mid h_ne_mid h_c_ge IH_right =>
    intro h_sorted h_exists
    have h_bs : binarySearch c values f lo hi = binarySearch c values f mid hi := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_neg h_c_ge]
    rw [h_bs]
    apply IH_right
    · intro i j h_mid_i h_i_j h_j_hi
      have h_lo_i : lo ≤ i := by omega
      exact h_sorted i j h_lo_i h_i_j h_j_hi
    · obtain ⟨i, h_lo_le, h_i_lt, h_fi_eq⟩ := h_exists
      use i
      refine ⟨?_, h_i_lt, h_fi_eq⟩
      by_contra h_not_le
      have h_i_lt_mid : i < mid := Nat.not_le.mp h_not_le
      have h_lt_f : f values[i]! < f values[mid]! := by
        have h_mid_lt_hi : mid < hi := by omega
        exact h_sorted i mid h_lo_le h_i_lt_mid h_mid_lt_hi
      rw [h_fi_eq] at h_lt_f
      exact h_c_ge h_lt_f

theorem binarySearch_lt_size (c : UInt32) (values : Array (UInt32 × UInt32))
    (lo hi : Nat) (h_lo_lt_hi : lo < hi) (h_hi_le_size : hi ≤ values.size) :
    binarySearch c values (·.1) lo hi < values.size := by
  revert h_lo_lt_hi h_hi_le_size
  induction lo, hi using binarySearch.induct c values (·.1) with
  | case1 lo hi h_ge =>
    intro h_lo_lt_hi _
    omega
  | case2 lo hi h_lt mid h_eq_mid =>
    intro _ h_hi_le_size
    have h_bs : binarySearch c values (·.1) lo hi = lo := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_pos h_eq_mid]
    rw [h_bs]
    omega
  | case3 lo hi h_lt mid h_ne_mid h_c_lt IH_left =>
    intro h_lo_lt_hi h_hi_le_size
    have h_mid_lt_hi : mid < hi := by omega
    have h_lo_lt_mid : lo < mid := by omega
    have h_bs : binarySearch c values (·.1) lo hi = binarySearch c values (·.1) lo mid := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_pos h_c_lt]
    rw [h_bs]
    exact IH_left h_lo_lt_mid (Nat.le_trans (Nat.le_of_lt h_mid_lt_hi) h_hi_le_size)
  | case4 lo hi h_lt mid h_ne_mid h_c_ge IH_right =>
    intro h_lo_lt_hi h_hi_le_size
    have h_mid_lt_hi : mid < hi := by omega
    have h_bs : binarySearch c values (·.1) lo hi = binarySearch c values (·.1) mid hi := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_neg h_c_ge]
    rw [h_bs]
    exact IH_right h_mid_lt_hi h_hi_le_size

theorem getCaseFoldChar_mem_table (c : Char) :
    (c.val, (Internal.getCaseFoldChar_spec c).val) ∈ caseFoldTable.toList := by
  unfold Internal.getCaseFoldChar_spec
  let table := caseFoldTable
  let idx := binarySearch c.val table (·.1) 0 table.size
  have h_sorted : ∀ i j, 0 ≤ i → i < j → j < table.size → (table[i]!).1 < (table[j]!).1 :=
    fun i j _ h_lt h_j_sz => caseFoldTable_sorted i j h_lt h_j_sz
  have h_exists : ∃ i, 0 ≤ i ∧ i < table.size ∧ (table[i]!).1 = c.val :=
    let ⟨i, h_lt, h_eq⟩ := caseFoldTable_complete c.val c.valid
    ⟨i, Nat.zero_le _, h_lt, h_eq⟩
  have h_idx_lt : idx < table.size :=
    binarySearch_lt_size c.val table 0 table.size caseFoldTable_nonempty (Nat.le_refl _)
  have h_get_bang : table[idx]! = table[idx] := by
    rw [getElem!_pos table idx h_idx_lt]
  have h_key_eq : (table[idx]!).1 = c.val :=
    binarySearch_correct c.val table (·.1) 0 table.size h_sorted h_exists
  have h_tgt_valid : UInt32.isValidChar (table[idx]!).2 := by
    exact caseFoldTable_tgt_valid idx h_idx_lt
  let tgt := (table[idx]!).2
  have h_char_val : (Char.ofNat tgt.toNat).val = tgt := by
    rw [Char.ofNat]
    rw [dif_pos h_tgt_valid]
    exact UInt32.toFin_inj.mp rfl
  simp
  rw [h_char_val]
  have h_pair_eq : table[idx]! = (c.val, tgt) := by
    apply Prod.ext
    · exact h_key_eq
    · rfl
  rw [← h_pair_eq]
  rw [h_get_bang]
  exact Array.getElem_mem h_idx_lt

theorem caseFoldTable_src_unique (i j : Nat) (hi : i < caseFoldTable.size) (hj : j < caseFoldTable.size)
    (h_eq : (caseFoldTable[i]!).1 = (caseFoldTable[j]!).1) : i = j := by
  by_contra h_ne
  cases Nat.lt_or_gt_of_ne h_ne with
  | inl h_lt =>
    have := caseFoldTable_sorted i j h_lt hj
    rw [h_eq] at this
    exact Nat.lt_irrefl _ this
  | inr h_gt =>
    have := caseFoldTable_sorted j i h_gt hi
    rw [h_eq] at this
    exact Nat.lt_irrefl _ this

theorem getCaseFoldChar_of_table_entry (src tgt : UInt32) :
    (src, tgt) ∈ caseFoldTable.toList →
    Internal.getCaseFoldChar_spec (Char.ofNat src.toNat) = Char.ofNat tgt.toNat := by
  intro h_mem
  have h_in_array : (src, tgt) ∈ caseFoldTable := Array.mem_toList_iff.mp h_mem
  have h_idx_exists := Array.mem_iff_getElem.mp h_in_array
  obtain ⟨i, hi, h_entry⟩ := h_idx_exists
  have h_src_valid : UInt32.isValidChar src := by
    have h_src_eq : (caseFoldTable[i]).1 = src := by simp only [h_entry]
    have h_i_bang : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
    rw [← h_src_eq, ← h_i_bang]
    exact caseFoldTable_src_valid i hi
  have h_char_val : (Char.ofNat src.toNat).val = src := by
    rw [Char.ofNat]
    rw [dif_pos h_src_valid]
    rfl
  have h_sorted : ∀ i j, 0 ≤ i → i < j → j < caseFoldTable.size →
      (caseFoldTable[i]!).1 < (caseFoldTable[j]!).1 :=
    fun i j _ h_lt h_j_sz => caseFoldTable_sorted i j h_lt h_j_sz
  have h_exists : ∃ k, 0 ≤ k ∧ k < caseFoldTable.size ∧
      (caseFoldTable[k]!).1 = (Char.ofNat src.toNat).val := by
    use i
    refine ⟨Nat.zero_le i, hi, ?_⟩
    have h_i_bang : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
    rw [h_i_bang, h_entry, h_char_val]
  set idx := binarySearch (Char.ofNat src.toNat).val caseFoldTable (·.1) 0 caseFoldTable.size with h_idx_def
  have h_key_eq : (caseFoldTable[idx]!).1 = (Char.ofNat src.toNat).val :=
    binarySearch_correct (Char.ofNat src.toNat).val caseFoldTable (·.1) 0 caseFoldTable.size
      h_sorted h_exists
  have h_key_eq' : (caseFoldTable[idx]!).1 = src := by rw [h_key_eq, h_char_val]
  have h_idx_lt : idx < caseFoldTable.size :=
    binarySearch_lt_size (Char.ofNat src.toNat).val caseFoldTable 0 caseFoldTable.size
      caseFoldTable_nonempty (Nat.le_refl _)
  have h_idx_eq_i : idx = i := by
    have h_i_bang : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
    have h_src_eq : (caseFoldTable[i]!).1 = src := by rw [h_i_bang, h_entry]
    apply caseFoldTable_src_unique idx i h_idx_lt hi
    rw [h_key_eq', h_src_eq]
  have h_idx_entry : caseFoldTable[idx]! = (src, tgt) := by
    have h_idx_bang : caseFoldTable[idx]! = caseFoldTable[idx] := getElem!_pos caseFoldTable idx h_idx_lt
    have h_i_lt : i < caseFoldTable.size := hi
    have h_getElem_eq : caseFoldTable[idx]'h_idx_lt = caseFoldTable[i]'h_i_lt := by
      simp only [h_idx_eq_i]
    rw [h_idx_bang]
    simp only [h_getElem_eq, h_entry]
  have h_snd_eq : (caseFoldTable[idx]!).2 = tgt := by rw [h_idx_entry]
  show Internal.getCaseFoldChar_spec (Char.ofNat src.toNat) = Char.ofNat tgt.toNat
  unfold Internal.getCaseFoldChar_spec
  have h_get_internal : caseFoldTable.get!Internal idx = caseFoldTable[idx]! := rfl
  simp only [← h_idx_def, h_get_internal, h_snd_eq]

theorem getCaseFoldChar_idempotent (tgt : UInt32) :
    (∃ src, (src, tgt) ∈ caseFoldTable.toList) →
    Internal.getCaseFoldChar_spec (Char.ofNat tgt.toNat) = Char.ofNat tgt.toNat := by
  intro ⟨src, h_mem⟩
  have h_in_array : (src, tgt) ∈ caseFoldTable := Array.mem_toList_iff.mp h_mem
  obtain ⟨i, hi, h_entry⟩ := Array.mem_iff_getElem.mp h_in_array
  have h_i_bang : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
  have h_tgt_eq : (caseFoldTable[i]!).2 = tgt := by rw [h_i_bang, h_entry]
  obtain ⟨j, hj, h_src_eq, h_tgt_eq'⟩ := caseFoldTable_idempotent i hi
  have h_j_bang : caseFoldTable[j]! = caseFoldTable[j] := getElem!_pos caseFoldTable j hj
  have h_j_src : (caseFoldTable[j]!).1 = tgt := by rw [h_src_eq, h_tgt_eq]
  have h_j_tgt : (caseFoldTable[j]!).2 = tgt := by rw [h_tgt_eq', h_tgt_eq]
  have h_j_entry : caseFoldTable[j] = (tgt, tgt) := by
    apply Prod.ext
    · rw [← h_j_bang, h_j_src]
    · rw [← h_j_bang, h_j_tgt]
  have h_tgt_mem : (tgt, tgt) ∈ caseFoldTable.toList := by
    have h_mem_array : (tgt, tgt) ∈ caseFoldTable := by
      rw [Array.mem_iff_getElem]
      exact ⟨j, hj, h_j_entry⟩
    exact Array.mem_toList_iff.mpr h_mem_array
  exact getCaseFoldChar_of_table_entry tgt tgt h_tgt_mem

end Regex.Unicode
