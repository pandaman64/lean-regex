import Regex.Data.SparseSet

namespace Regex.Data.SparseSet

theorem mem_insert_of_mem {s : SparseSet n} {i j : Fin n} : i ∈ s → i ∈ s.insert j := by
  intro h
  unfold SparseSet.insert
  split
  next => exact h
  next hmem =>
    simp [mem, Vec.get_set]
    if heq : j.val = i.val then
      simp [heq]
      exact Fin.eq_of_val_eq heq
    else
      simp [mem] at h
      simp [heq]
      have : s.count ≠ s.sparse[i.val].val := Nat.ne_of_gt h.left
      simp [this, h]
      exact Nat.lt_trans h.left (Nat.lt_succ_self _)

theorem eq_or_mem_of_mem_insert {s : SparseSet n} {i j : Fin n} : i ∈ s.insert j → i = j ∨ i ∈ s := by
  intro h
  if heq : i = j then
    exact Or.inl heq
  else
    suffices i ∈ s from Or.inr this
    unfold SparseSet.insert at h
    split at h
    next => exact h
    next hmem =>
      have ne : j.val ≠ i.val := Ne.symm (Fin.val_ne_of_ne heq)
      simp [mem, Vec.get_set, ne] at h
      split at h
      case isTrue heq' => simp [h] at heq
      case isFalse heq' =>
        have : s.sparse[i.val] < s.count := by
          have : s.sparse[i.val] ≤ s.count := Nat.le_of_lt_succ h.left
          exact Nat.lt_of_le_of_ne this (Ne.symm heq')
        simp [mem, this, h]

theorem subset_self {s : SparseSet n} : s ⊆ s := by
  simp [HasSubset.Subset, Subset]

theorem mem_of_mem_of_subset {s₁ s₂ : SparseSet n} {i : Fin n} (mem : i ∈ s₁) (sub : s₁ ⊆ s₂) : i ∈ s₂ :=
  sub i mem

theorem subset_insert {s : SparseSet n} : s ⊆ s.insert i := by
  intro j hj
  exact mem_insert_of_mem hj

theorem subset_trans {s₁ s₂ s₃ : SparseSet n} (h₁ : s₁ ⊆ s₂) (h₂ : s₂ ⊆ s₃) : s₁ ⊆ s₃ := by
  intro i hi
  exact h₂ _ (h₁ _ hi)

instance : Trans (· ⊆ · : SparseSet n → SparseSet n → Prop) (· ⊆ · : SparseSet n → SparseSet n → Prop) (· ⊆ · : SparseSet n → SparseSet n → Prop) where
  trans := subset_trans

theorem mem_get {s : SparseSet n} {i : Nat} (h : i < s.count) : s[i] ∈ s := by
  have isLt : i < n := Nat.lt_of_lt_of_le h s.le_count
  have : s[i] = s.dense[i] := rfl
  simp [mem, this]
  have := s.sparse_dense ⟨i, isLt⟩ h
  simp at this
  simp [this, h]

end Regex.Data.SparseSet
