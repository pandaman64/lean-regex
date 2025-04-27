import Regex.Data.BitVec

set_option autoImplicit false

namespace Regex.Data

@[ext]
structure BitMatrix (w h : Nat) where
  bv : BitVec (w * h)
deriving Repr

namespace BitMatrix

variable {w h : Nat}

instance : ToString (BitMatrix w h) := ⟨fun m => toString m.bv⟩

def zero (w h : Nat) : BitMatrix w h := ⟨BitVec.zero _⟩

def index {w h : Nat} (x : Fin w) (y : Fin h) : Fin (w * h) :=
  have : y.val * w + x.val < w * h := by
    calc y.val * w + x.val
      _ < y.val * w + w := by omega
      _ = (y.val + 1) * w := (Nat.succ_mul _ _).symm
      _ ≤ h * w := Nat.mul_le_mul_right w (by omega)
      _ = w * h := Nat.mul_comm _ _
  ⟨y.val * w + x.val, this⟩

theorem index_ne_of_ne_x {w h : Nat} (x x' : Fin w) (y y' : Fin h) (hx : x ≠ x') : index x y ≠ index x' y' := by
  simp [index]
  intro eq
  have : (y * w + x) % w = (y' * w + x') % w := by rw [eq]
  simp [Nat.add_mod, Nat.mod_eq_of_lt] at this
  exact (Fin.val_ne_of_ne hx) this

theorem index_ne_of_ne_y {w h : Nat} (x x' : Fin w) (y y' : Fin h) (hy : y ≠ y') : index x y ≠ index x' y' := by
  simp [index]
  intro eq
  cases Nat.lt_or_gt_of_ne (Fin.val_ne_of_ne hy) with
  | inl lt =>
    have : y.val * w + x.val < y'.val * w + x'.val := by
      calc y.val * w + x.val
        _ < y.val * w + w := by omega
        _ = (y.val + 1) * w := by rw [Nat.succ_mul]
        _ ≤ y'.val * w := by exact Nat.mul_le_mul_right w lt
        _ ≤ y'.val * w + x'.val := by omega
    omega
  | inr gt =>
    have : y.val * w + x.val > y'.val * w + x'.val := by
      calc y'.val * w + x'.val
        _ < y'.val * w + w := by omega
        _ = (y'.val + 1) * w := by rw [Nat.succ_mul]
        _ ≤ y.val * w := by exact Nat.mul_le_mul_right w gt
        _ ≤ y.val * w + x.val := by omega
    omega

theorem index_ne_of_ne {w h : Nat} (x x' : Fin w) (y y' : Fin h) (hne : x ≠ x' ∨ y ≠ y') : index x y ≠ index x' y' := by
  cases hne with
  | inl hx => exact index_ne_of_ne_x x x' y y' hx
  | inr hy => exact index_ne_of_ne_y x x' y y' hy

def get (m : BitMatrix w h) (x : Fin w) (y : Fin h) : Bool := m.bv[index x y]

@[simp]
theorem get_zero {w h : Nat} (x : Fin w) (y : Fin h) : (zero w h).get x y = false := by
  simp [zero, get]

@[ext]
theorem eq_of_get_eq {m m' : BitMatrix w h} (eq : ∀ x y, m.get x y = m'.get x y) : m = m' := by
  simp [get, index] at eq
  ext i lt
  let x := i % w
  let y := i / w
  have eq' : i = y * w + x := by
    rw [Nat.mul_comm, Nat.div_add_mod i w]
  have lt' : 0 < w := by
    apply Nat.pos_of_ne_zero
    intro eqw
    simp [eqw] at lt
  simp [eq', eq ⟨x, Nat.mod_lt i lt'⟩ ⟨y, Nat.div_lt_of_lt_mul lt⟩]

def set (m : BitMatrix w h) (x : Fin w) (y : Fin h) : BitMatrix w h :=
  ⟨m.bv.set (index x y)⟩

theorem get_set_eq {m : BitMatrix w h} (x : Fin w) (y : Fin h) : (m.set x y).get x y := by
  show (m.bv.set (index x y).val)[(index x y).val]
  rw [BitVec.getElem_set_eq]

theorem get_set_ne {m : BitMatrix w h} (x x' : Fin w) (y y' : Fin h) (hne : x ≠ x' ∨ y ≠ y') : (m.set x y).get x' y' = m.get x' y' := by
  show (m.bv.set (index x y).val)[(index x' y').val] = m.bv[(index x' y').val]
  have : (index x y).val ≠ (index x' y').val := Fin.val_ne_of_ne (index_ne_of_ne x x' y y' hne)
  rw [BitVec.getElem_set_ne m.bv _ _ (index x y).isLt (index x' y').isLt this]

theorem get_set {m : BitMatrix w h} (x x' : Fin w) (y y' : Fin h) : (m.set x y).get x' y' = decide ((x = x' ∧ y = y') ∨ m.get x' y') := by
  if h : x = x' ∧ y = y' then
    simp [h, get_set_eq]
  else
    simp [h, get_set_ne x x' y y' (by omega)]

theorem get_set_of_get {m : BitMatrix w h} {x x' : Fin w} {y y' : Fin h} (h : m.get x y) : (m.set x' y').get x y := by
  simp [get_set, h]

theorem eq_set_of_get {m : BitMatrix w h} {x : Fin w} {y : Fin h} (h : m.get x y) : m.set x y = m := by
  ext x' y'
  simp [get_set]
  intro eq₁ eq₂
  exact eq₁ ▸ eq₂ ▸ h

def popcount (m : BitMatrix w h) : Nat := m.bv.popcount

theorem popcount_le {m : BitMatrix w h} : popcount m ≤ w * h := BitVec.popcount_le m.bv

theorem popcount_decreasing (m : BitMatrix w h) (x : Fin w) (y : Fin h) (hget : ¬m.get x y) : w * h + 1 - popcount (m.set x y) < w * h + 1 - popcount m :=
  BitVec.sub_lt_popcount_set_not_getElem m.bv (index x y).val (index x y).isLt hget

end BitMatrix

end Regex.Data
