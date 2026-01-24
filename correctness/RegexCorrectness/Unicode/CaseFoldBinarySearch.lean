
import Regex.Unicode.CaseFold
import Std.Data.HashMap
import Mathlib.Data.List.Basic

set_option autoImplicit false

open Regex.Unicode

namespace Regex.Unicode

axiom caseFoldTable_sorted :
    ∀ i j : Nat, i < j → j < caseFoldTable.size →
    (caseFoldTable[i]!).1 < (caseFoldTable[j]!).1

axiom caseFoldTable_nonempty : caseFoldTable.size > 0

axiom caseFoldTable_src_valid :
    ∀ i : Nat, i < caseFoldTable.size → UInt32.isValidChar (caseFoldTable[i]!).1

axiom caseFoldTable_tgt_valid :
    ∀ i : Nat, i < caseFoldTable.size → UInt32.isValidChar (caseFoldTable[i]!).2

axiom caseFoldTable_idempotent (i : Nat) (hi : i < caseFoldTable.size) :
    ∃ j : Nat, j < caseFoldTable.size ∧
      (caseFoldTable[j]!).1 = (caseFoldTable[i]!).2 ∧
      (caseFoldTable[j]!).2 = (caseFoldTable[i]!).2

theorem binarySearch_fins_key {α} [Inhabited α] (c : UInt32) (values : Array α) (f : α → UInt32)
    (lo hi : Nat)
    (h_sorted : ∀ i j, lo ≤ i → i < j → j < hi → f (values[i]!) < f (values[j]!))
    (h_exists : ∃ i, lo ≤ i ∧ i < hi ∧ f (values[i]!) = c) :
    f (values[binarySearch c values f lo hi]!) = c := by
  revert h_sorted h_exists
  induction lo, hi using binarySearch.induct c values f with
  | case1 lo hi h_ge =>
    intro _ h_exists
    obtain ⟨_, h_lo_le, h_i_lt, _⟩ := h_exists
    omega
  | case2 lo hi h_lt mid h_eq_mid =>
    intro _ h_exists
    obtain ⟨i, h_lo_le, h_i_lt, h_fi_eq⟩ := h_exists
    have h_i_eq : i = lo := by omega
    have h_bs : binarySearch c values f lo hi = lo := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_pos h_eq_mid]
    rw [h_bs, ← h_i_eq, h_fi_eq]
  | case3 lo hi h_lt mid h_ne_mid h_c_lt ih_left =>
    intro h_sorted h_exists
    have h_bs : binarySearch c values f lo hi = binarySearch c values f lo mid := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_pos h_c_lt]
    rw [h_bs]
    apply ih_left
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
  | case4 lo hi h_lt mid h_ne_mid h_c_ge ih_right =>
    intro h_sorted h_exists
    have h_bs : binarySearch c values f lo hi = binarySearch c values f mid hi := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_neg h_c_ge]
    rw [h_bs]
    apply ih_right
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
  | case3 lo hi h_lt mid h_ne_mid h_c_lt ih_left =>
    intro _ h_hi_le_size
    have h_bs : binarySearch c values (·.1) lo hi = binarySearch c values (·.1) lo mid := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_pos h_c_lt]
    rw [h_bs]
    exact ih_left (by omega) (by omega)
  | case4 lo hi h_lt mid h_ne_mid h_c_ge ih_right =>
    intro _ h_hi_le_size
    have h_bs : binarySearch c values (·.1) lo hi = binarySearch c values (·.1) mid hi := by
      rw [binarySearch.eq_def]
      simp only [ge_iff_le, h_lt, ite_false]
      rw [if_neg h_ne_mid, if_neg h_c_ge]
    rw [h_bs]
    exact ih_right (by omega) h_hi_le_size

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

theorem getCaseFoldChar_eq_of_mem (src tgt : UInt32) :
    (src, tgt) ∈ caseFoldTable.toList →
    Internal.getCaseFoldChar_spec (Char.ofNat src.toNat) = Char.ofNat tgt.toNat := by
  intro h_mem
  have h_in_array : (src, tgt) ∈ caseFoldTable := Array.mem_toList_iff.mp h_mem
  obtain ⟨i, hi, h_entry⟩ := Array.mem_iff_getElem.mp h_in_array
  have h_getElem!_eq_i : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
  have h_src_valid : UInt32.isValidChar src := by
    have h_src_eq : (caseFoldTable[i]).1 = src := by simp only [h_entry]
    rw [← h_src_eq, ← h_getElem!_eq_i]
    exact caseFoldTable_src_valid i hi
  have h_char_val : (Char.ofNat src.toNat).val = src := by
    rw [Char.ofNat, dif_pos h_src_valid]
    rfl
  have h_sorted : ∀ i j, 0 ≤ i → i < j → j < caseFoldTable.size →
      (caseFoldTable[i]!).1 < (caseFoldTable[j]!).1 :=
    fun i j _ h_lt h_j_sz => caseFoldTable_sorted i j h_lt h_j_sz
  have h_exists : ∃ k, 0 ≤ k ∧ k < caseFoldTable.size ∧
      (caseFoldTable[k]!).1 = (Char.ofNat src.toNat).val := by
    exact ⟨i, Nat.zero_le i, hi, by rw [h_getElem!_eq_i, h_entry, h_char_val]⟩
  set idx := binarySearch (Char.ofNat src.toNat).val caseFoldTable (·.1) 0 caseFoldTable.size with h_idx_def
  have h_idx_lt : idx < caseFoldTable.size :=
    binarySearch_lt_size (Char.ofNat src.toNat).val caseFoldTable 0 caseFoldTable.size
      caseFoldTable_nonempty (Nat.le_refl _)
  unfold Internal.getCaseFoldChar_spec
  have h_get_internal : caseFoldTable.get!Internal idx = caseFoldTable[idx]! := rfl
  simp only [← h_idx_def, h_get_internal]
  split
  case isTrue h_src_eq =>
    have h_idx_src : (caseFoldTable[idx]!).1 = (Char.ofNat src.toNat).val := by
      have := binarySearch_fins_key (Char.ofNat src.toNat).val caseFoldTable (·.1) 0 caseFoldTable.size
        (fun i j _ h_i_lt_j h_j_sz => caseFoldTable_sorted i j h_i_lt_j h_j_sz)
        ⟨i, Nat.zero_le i, hi, by rw [h_getElem!_eq_i, h_entry, h_char_val]⟩
      exact this
    have h_idx_eq_i : idx = i := by
      apply caseFoldTable_src_unique idx i h_idx_lt hi
      rw [h_idx_src, h_char_val, h_getElem!_eq_i, h_entry]
    have h_idx_tgt : (caseFoldTable[idx]!).2 = tgt := by
      rw [h_idx_eq_i, h_getElem!_eq_i, h_entry]
    simp only [h_idx_tgt]
  case isFalse h =>
    exfalso
    have h_idx_src : (caseFoldTable[idx]!).1 = (Char.ofNat src.toNat).val := by
      have := binarySearch_fins_key (Char.ofNat src.toNat).val caseFoldTable (·.1) 0 caseFoldTable.size
        (fun i j _ h_i_lt_j h_j_sz => caseFoldTable_sorted i j h_i_lt_j h_j_sz)
        ⟨i, Nat.zero_le i, hi, by rw [h_getElem!_eq_i, h_entry, h_char_val]⟩
      exact this
    simp only [beq_iff_eq, h_idx_src, not_true_eq_false] at h

theorem getCaseFoldChar_fixed_of_is_target (tgt : UInt32) :
    (∃ src, (src, tgt) ∈ caseFoldTable.toList) →
    Internal.getCaseFoldChar_spec (Char.ofNat tgt.toNat) = Char.ofNat tgt.toNat := by
  intro ⟨src, h_mem⟩
  have h_in_array : (src, tgt) ∈ caseFoldTable := Array.mem_toList_iff.mp h_mem
  obtain ⟨i, hi, h_entry⟩ := Array.mem_iff_getElem.mp h_in_array
  have h_getElem!_eq_i : caseFoldTable[i]! = caseFoldTable[i] := getElem!_pos caseFoldTable i hi
  have h_tgt_eq : (caseFoldTable[i]!).2 = tgt := by rw [h_getElem!_eq_i, h_entry]
  obtain ⟨j, hj, h_src_eq, h_tgt_eq'⟩ := caseFoldTable_idempotent i hi
  have h_getElem!_eq_j : caseFoldTable[j]! = caseFoldTable[j] := getElem!_pos caseFoldTable j hj
  have h_j_src : (caseFoldTable[j]!).1 = tgt := by rw [h_src_eq, h_tgt_eq]
  have h_j_tgt : (caseFoldTable[j]!).2 = tgt := by rw [h_tgt_eq', h_tgt_eq]
  have h_j_entry : caseFoldTable[j] = (tgt, tgt) :=
    Prod.ext (by rw [← h_getElem!_eq_j, h_j_src]) (by rw [← h_getElem!_eq_j, h_j_tgt])
  have h_tgt_mem : (tgt, tgt) ∈ caseFoldTable.toList := by
    rw [Array.mem_toList_iff, Array.mem_iff_getElem]
    exact ⟨j, hj, h_j_entry⟩
  exact getCaseFoldChar_eq_of_mem tgt tgt h_tgt_mem

end Regex.Unicode
