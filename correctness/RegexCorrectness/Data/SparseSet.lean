import Regex.Data.SparseSet

namespace Regex.Data.SparseSet

theorem mem_insert_of_mem {s : SparseSet n} {i j : Fin n} (h : j ∉ s) (hmem : i ∈ s) : i ∈ s.insert j h := by
  have ne : i ≠ j := fun eq => h (eq ▸ hmem)
  simp [mem] at hmem
  simp [insert, mem, Vector.getElem_set_ne (h := Fin.val_ne_of_ne ne.symm)]
  grind

theorem eq_or_mem_of_mem_insert {s : SparseSet n} {i j : Fin n} {h : j ∉ s} : i ∈ s.insert j h → i = j ∨ i ∈ s := by
  simp [insert, mem]
  grind only [Vector.getElem_set, cases Or]

theorem subset_self {s : SparseSet n} : s ⊆ s := by
  simp [HasSubset.Subset, Subset]

theorem mem_of_mem_of_subset {s₁ s₂ : SparseSet n} {i : Fin n} (mem : i ∈ s₁) (sub : s₁ ⊆ s₂) : i ∈ s₂ :=
  sub i mem

theorem subset_insert {s : SparseSet n} {h : i ∉ s} : s ⊆ s.insert i h := by
  intro j hj
  exact mem_insert_of_mem h hj

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

def index (i : Fin n) (s : SparseSet n) : Nat := s.sparse[i]

theorem index_of_mem {i : Fin n} {s : SparseSet n} (h : i ∈ s) : ∃ _ : s.index i < s.count, s[s.index i] = i := by
  simp [mem] at h
  exact ⟨h.1, by simpa [getElem, get, index] using h.2⟩

end Regex.Data.SparseSet
