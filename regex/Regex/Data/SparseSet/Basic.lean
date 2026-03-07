module
import Init.Data.Vector.Lemmas
import Regex.Data.SparseSet.Bijection

set_option autoImplicit false

namespace Regex.Data

public structure SparseSet (n : Nat) where
  count : Nat
  dense : Vector (Fin n) n
  sparse : Vector (Fin n) n
  sparse_dense : ∀ i : Fin n, i < count → sparse[dense[i.val].val] = i
  le_count : count ≤ n

-- Prints only the members
instance {n} : Repr (SparseSet n) where
  reprPrec s i := reprPrec s.dense.toArray[0:s.count] i

instance {n} : ToString (SparseSet n) where
  toString s := toString s.dense.toArray[0:s.count]

namespace SparseSet

variable {n : Nat} {s : SparseSet n} {i j : Fin n}

theorem sparse_dense_fin (h : i < s.count) : s.sparse[s.dense[i]] = i :=
  s.sparse_dense i h

@[inline]
public def mem (s : SparseSet n) (i : Fin n) : Bool :=
  s.sparse[i] < s.count && s.dense[s.sparse[i]] == i

public instance : Membership (Fin n) (SparseSet n) where
  mem s i := s.mem i

@[simp]
theorem mem_mem : i ∈ s ↔ s.mem i := Iff.rfl

public def Subset ⦃n : Nat⦄ (s₁ s₂ : SparseSet n) : Prop :=
  ∀ i, i ∈ s₁ → i ∈ s₂

public instance : HasSubset (SparseSet n) where
  Subset := @Subset n

@[inline]
public instance : Decidable (i ∈ s) :=
  match h : s.mem i with
  | true => isTrue h
  | false => isFalse (by simp [h])

theorem mem_dense_of_lt (h : i < s.count) : s.dense[i] ∈ s := by
  simp [mem, sparse_dense, h]

theorem dense_inj (hi : i < s.count) (hj : j < s.count) (eq : s.dense[i] = s.dense[j]) :
  i = j := by
  have : s.sparse[s.dense[i]] = s.sparse[s.dense[j]] := by grind
  simpa [s.sparse_dense i hi, s.sparse_dense j hj]

theorem dense_surj (h : j ∈ s) : ∃ i : Fin n, i < s.count ∧ s.dense[i] = j := by
  simp [mem] at h
  exists s.sparse[j]

theorem dense_sparse_of_full (h : n = s.count) (j : Fin n) : s.dense[s.sparse[j]] = j := by
  let f (i : Fin n) : Fin n := s.dense[i]
  have leftInv : Function.LeftInverse (fun j => s.sparse[j]) f := by
    grind [s.sparse_dense]
  have inj : Function.Injective f := leftInv.injective
  have surj : Function.Surjective f := Bijection.surj_of_inj f inj
  grind [surj j]

theorem lt_of_not_mem (i : Fin n) (h : i ∉ s) : s.count < n := by
  simp only [mem_mem, mem, Fin.getElem_fin, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    not_and] at h
  refine Decidable.byContradiction fun nlt => ?_
  have eq : n = s.count := by grind [s.le_count]
  exact h (by grind) (dense_sparse_of_full eq i)

public section

def empty {n : Nat} : SparseSet n :=
  let v := Vector.ofFn (fun x : Fin n => ⟨0, x.pos⟩)
  ⟨0, v, v, fun _ _ => by contradiction, Nat.zero_le _⟩

def insert (s : SparseSet n) (i : Fin n) (mem : i ∉ s) : SparseSet n :=
  have isLt : s.count < n := lt_of_not_mem i mem
  let dense' := s.dense.set s.count i
  let sparse' := s.sparse.set i ⟨s.count, isLt⟩
  have sparse_dense' (j : Fin n) (h : j < s.count + 1) : sparse'[dense'[j]] = j := by
    cases Nat.eq_or_lt_of_le (Nat.le_of_succ_le_succ h) with
    | inl eq => grind
    | inr lt =>
      have : dense'[j] = s.dense[j] := by grind
      grind [mem_dense_of_lt, s.sparse_dense]
  ⟨s.count + 1, dense', sparse', sparse_dense', isLt⟩

@[simp]
theorem mem_insert (h : i ∉ s) : i ∈ s.insert i h := by
  unfold insert
  simp [mem]

def clear (s : SparseSet n) : SparseSet n :=
  ⟨0, s.dense, s.sparse, fun _ _ => by contradiction, Nat.zero_le _⟩

def isEmpty (s : SparseSet n) : Bool := s.count = 0

@[simp]
theorem isEmpty_empty : (@empty n).isEmpty := (rfl)

@[simp]
theorem isEmpty_clear : s.clear.isEmpty := (rfl)

@[simp]
theorem not_mem_of_isEmpty (h : s.isEmpty) : ¬ i ∈ s := by
  intro m
  simp [isEmpty] at h
  simp [mem, h] at m

@[inline]
def get (s : SparseSet n) (i : Nat) (h : i < s.count) : Fin n :=
  s.dense[i]'(Nat.lt_of_lt_of_le h s.le_count)

@[inline]
instance : GetElem (SparseSet n) Nat (Fin n) (fun s i => i < s.count) where
  getElem := get

-- Termination measure for `SparseSet`
def measure (s : SparseSet n) : Nat := n - s.count

theorem measure_insert (h : i ∉ s) : (s.insert i h).measure = s.measure - 1 := by
  simp [measure, insert, Nat.sub_add_eq]

theorem lt_measure_insert (h : ¬s.mem i) : (s.insert i h).measure < s.measure := by
  simp [measure, insert, Nat.sub_add_eq]
  refine Nat.sub_lt ?_ (by decide)
  exact Nat.zero_lt_sub_of_lt (lt_of_not_mem i (by simp [h]))

theorem lt_measure_insert' (h : i ∉ s) : (s.insert i h).measure < s.measure :=
  lt_measure_insert h

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply SparseSet.lt_measure_insert; assumption)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply SparseSet.lt_measure_insert'; assumption)

end

end SparseSet

end Regex.Data
