import Init.Data.Vector.Lemmas
import Regex.Data.SparseSet.Bijection

namespace Regex.Data

structure SparseSet (n : Nat) where
  count : Nat
  dense : Vector (Fin n) n
  sparse : Vector (Fin n) n
  sparse_dense : ∀ i : Fin n, i < count → sparse[dense[i.val].val] = i
  le_count : count ≤ n

-- Prints only the members
instance : Repr (SparseSet n) where
  reprPrec s i := reprPrec s.dense.toArray[0:s.count] i

instance : ToString (SparseSet n) where
  toString s := toString s.dense.toArray[0:s.count]

namespace SparseSet

variable {n : Nat} {s : SparseSet n} {i j : Fin n}

open Bijection

def empty {n : Nat} : SparseSet n :=
  let v := Vector.ofFn (fun x : Fin n => ⟨0, x.pos⟩)
  ⟨0, v, v, fun _ _ => by contradiction, Nat.zero_le _⟩

theorem sparse_dense_fin (h : i < s.count) : s.sparse[s.dense[i]] = i :=
  s.sparse_dense i h

@[inline]
def mem (s : SparseSet n) (i : Fin n) : Bool :=
  s.sparse[i] < s.count && s.dense[s.sparse[i]] == i

instance : Membership (Fin n) (SparseSet n) where
  mem s i := s.mem i

@[simp]
theorem mem_mem : i ∈ s ↔ s.mem i := Iff.rfl

def Subset ⦃n : Nat⦄ (s₁ s₂ : SparseSet n) : Prop :=
  ∀ i, i ∈ s₁ → i ∈ s₂

instance : HasSubset (SparseSet n) where
  Subset := @Subset n

@[inline]
instance : Decidable (i ∈ s) :=
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

theorem dense_sparse_of_full (h : n ≤ s.count) : s.dense[s.sparse[j]] = j := by
  let f (i : Fin n) : Fin n := s.dense[i]
  have inj : inj f := by
    intro x y eq
    exact dense_inj (Nat.lt_of_lt_of_le x.isLt h) (Nat.lt_of_lt_of_le y.isLt h) eq
  have surj : surj f := surj_of_inj _ inj
  have ⟨i, eq⟩ := surj j
  simp [f, ←eq, s.sparse_dense i (Nat.lt_of_lt_of_le i.isLt h)]

theorem lt_of_mem (i : Fin n) (h : ¬i ∈ s) : s.count < n := by
  simp [SparseSet.mem] at h
  refine Decidable.byContradiction fun nlt => ?_
  have ge := Nat.le_of_not_lt nlt
  apply h (Nat.lt_of_lt_of_le s.sparse[i].isLt ge)
  exact dense_sparse_of_full ge

def insert (s : SparseSet n) (i : Fin n) (mem : i ∉ s) : SparseSet n :=
  let ⟨count, dense, sparse, sparse_dense, _⟩ := s
  have isLt : count < n := lt_of_mem i mem
  let dense' := dense.set count i
  let sparse' := sparse.set i ⟨count, isLt⟩
  have sparse_dense' (j : Fin n) (h : j < count + 1) : sparse'[dense'[j]] = j := by
    have : j ≤ count := Nat.le_of_succ_le_succ h
    cases Nat.eq_or_lt_of_le this with
    | inl eq =>
      simp [dense', sparse', eq, Vector.getElem_set_self]
      exact Fin.eq_of_val_eq eq.symm
    | inr lt =>
      have : dense'[j] = dense[j] := by
        simp [dense']
        rw [Vector.getElem_set_ne isLt (by omega) (by omega)]
      simp [sparse', this]
      rw [Vector.getElem_set]
      split
      case isTrue eq =>
        simp [SparseSet.mem] at mem
        have : sparse[i.val] = j := by
          simp [eq, sparse_dense j lt]
        simp [this, lt] at mem
        exact absurd (Fin.eq_of_val_eq eq.symm) mem
      case isFalse => exact sparse_dense j lt
  ⟨count + 1, dense', sparse', sparse_dense', isLt⟩

@[simp]
theorem mem_insert (h : i ∉ s) : i ∈ s.insert i h := by
  unfold insert
  simp [mem]

def clear (s : SparseSet n) : SparseSet n :=
  ⟨0, s.dense, s.sparse, fun _ _ => by contradiction, Nat.zero_le _⟩

def isEmpty (s : SparseSet n) : Bool := s.count = 0

@[simp]
theorem isEmpty_empty : (@empty n).isEmpty := rfl

@[simp]
theorem isEmpty_clear : s.clear.isEmpty := rfl

@[simp]
theorem not_mem_of_isEmpty (h : s.isEmpty) : ¬ i ∈ s := by
  intro m
  simp [isEmpty] at h
  simp [mem, h] at m

@[inline]
def foldl {α : Type} (f : α → Fin n → α) (init : α) (s : SparseSet n) : α :=
  go init 0 (Nat.zero_le _)
where
  @[specialize]
  go (accum : α) (i : Nat) (hle : i ≤ s.count) : α :=
    if h : i = s.count then
      accum
    else
      have hlt : i < s.count := Nat.lt_of_le_of_ne hle h
      have hlt' : i < n := Nat.lt_of_lt_of_le hlt s.le_count
      let v := s.dense[i]
      go (f accum v) (i + 1) hlt
  termination_by s.count - i

@[inline]
def get (s : SparseSet n) (i : Nat) (h : i < s.count) : Fin n :=
  s.dense[i]'(Nat.lt_of_lt_of_le h s.le_count)

@[inline]
instance : GetElem (SparseSet n) Nat (Fin n) (fun s i => i < s.count) where
  getElem := get

-- Termination measure for `SparseSet`
def measure (s : SparseSet n) : Nat := n - s.count

theorem measure_insert (h : ¬i ∈ s) : (s.insert i h).measure = s.measure - 1 := by
  simp [measure, insert, Nat.sub_add_eq]

theorem lt_measure_insert (h : ¬s.mem i) : (s.insert i h).measure < s.measure := by
  simp [measure, insert, Nat.sub_add_eq]
  refine Nat.sub_lt ?_ (by decide)
  exact Nat.zero_lt_sub_of_lt (lt_of_mem i (by simp [h]))

theorem lt_measure_insert' (h : ¬i ∈ s) : (s.insert i h).measure < s.measure :=
  lt_measure_insert h

macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply SparseSet.lt_measure_insert; assumption)
macro_rules | `(tactic| decreasing_trivial) => `(tactic| apply SparseSet.lt_measure_insert'; assumption)

end SparseSet

end Regex.Data
