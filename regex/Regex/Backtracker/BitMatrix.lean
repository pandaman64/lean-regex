import Regex.Data.BitVec

namespace Regex.Backtracker

structure BitMatrix (w h : Nat) where
  bv : BitVec (w * h)
deriving Repr

namespace BitMatrix

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

def get (m : BitMatrix w h) (x : Fin w) (y : Fin h) : Bool := m.bv[index x y]

def set (m : BitMatrix w h) (x : Fin w) (y : Fin h) : BitMatrix w h :=
  ⟨m.bv.set (index x y)⟩

def popcount (m : BitMatrix w h) : Nat := m.bv.popcount

theorem popcount_le {m : BitMatrix w h} : popcount m ≤ w * h := BitVec.popcount_le m.bv

theorem popcount_decreasing (m : BitMatrix w h) (x : Fin w) (y : Fin h) (hget : ¬m.get x y) : w * h + 1 - popcount (m.set x y) < w * h + 1 - popcount m :=
  BitVec.sub_lt_popcount_set_not_getElem m.bv (index x y).val (index x y).isLt hget

end BitMatrix

end Regex.Backtracker
