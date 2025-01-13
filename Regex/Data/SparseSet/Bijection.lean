-- Minimal theory about the bijection between `Fin n`.

set_option autoImplicit false

namespace Regex.Data.SparseSet.Bijection

def inj {α β} (f : α → β) := ∀ x y, f x = f y → x = y
def surj {α β} (f : α → β) := ∀ y, ∃ x, f x = y
def bij {α β} (f : α → β) := inj f ∧ surj f

theorem _root_.Fin.eq_of_ge {n} {i : Fin (n + 1)} (h : i ≥ n) : i = ⟨n, Nat.lt_succ_self n⟩ := by
  apply Fin.eq_of_val_eq
  exact Nat.le_antisymm (Nat.le_of_succ_le_succ i.isLt) h

theorem _root_.Fin.eq_of_not_lt {n} {i : Fin (n + 1)} (h : ¬ i < n) : i = ⟨n, Nat.lt_succ_self n⟩ :=
  Fin.eq_of_ge (Nat.ge_of_not_lt h)

theorem surj_of_inj {n} (f : Fin n → Fin n) (h : inj f) : surj f := by
  induction n with
  | zero =>
    intro y
    have : y.val < 0 := y.isLt
    contradiction
  | succ n ih =>
    let n' : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let f' (x : Fin n) : Fin n :=
      let x' : Fin (n + 1) := ⟨x.val, Nat.lt_trans x.isLt (Nat.lt_succ_self n)⟩
      let y := f x'
      if isLt : y.val < n then
        ⟨y.val, isLt⟩
      else
        have eqx : f x' = n' := Fin.eq_of_not_lt isLt
        have isLt : f n' < n' := by
          refine Decidable.byContradiction fun nlt => ?_
          have eqn : f n' = n' := Fin.eq_of_not_lt nlt
          have : f x' = f n' := by rw [eqx, eqn]
          have : x' = n' := h _ _ this
          have : x.val = n := by
            have : x'.val = n'.val := by rw [this]
            exact this
          exact Nat.lt_irrefl _ (this ▸ x.isLt)
        ⟨f ⟨n, Nat.lt_succ_self n⟩, isLt⟩
    have : inj f' := by
      intro x y eq
      let x' : Fin (n + 1) := ⟨x.val, Nat.lt_trans x.isLt (Nat.lt_succ_self n)⟩
      let y' : Fin (n + 1) := ⟨y.val, Nat.lt_trans y.isLt (Nat.lt_succ_self n)⟩

      if hx : f x' < n then
        if hy : f y' < n then
          simp [f', hx, hy] at eq
          have := h _ _ (Fin.eq_of_val_eq eq)
          simp at this
          exact Fin.eq_of_val_eq this
        else
          simp [f', hx, hy] at eq
          have := h _ _ (Fin.eq_of_val_eq eq)
          simp at this
          exact absurd (this ▸ x.isLt) (Nat.lt_irrefl _)
      else
        if hy : f y' < n then
          simp [f', hx, hy] at eq
          have := h _ _ (Fin.eq_of_val_eq eq)
          simp at this
          exact absurd (this.symm ▸ y.isLt) (Nat.lt_irrefl _)
        else
          have eqx := Fin.eq_of_not_lt hx
          have eqy := Fin.eq_of_not_lt hy
          have : f x' = f y' := by rw [eqx, eqy]
          have : x' = y' := h _ _ this
          have : x.val = y.val := by
            have : x'.val = y'.val := by rw [this]
            exact this
          exact Fin.eq_of_val_eq this
    have surj : surj f' := ih _ this

    intro y
    have : y.val ≤ n := Nat.le_of_succ_le_succ y.isLt

    if isLt : y.val < n then
      let ⟨x, eq⟩ := surj ⟨y.val, isLt⟩
      simp [f'] at eq
      split at eq
      case isTrue =>
        simp at eq
        exact ⟨⟨x.val, Nat.lt_trans x.isLt (Nat.lt_succ_self n)⟩, Fin.eq_of_val_eq eq⟩
      case isFalse =>
        simp at eq
        exact ⟨n', Fin.eq_of_val_eq eq⟩
    else
      have := Fin.eq_of_not_lt isLt
      simp [this]
      if isLt' : f n' < n then
        let ⟨x, eq⟩ := surj ⟨(f n').val, isLt'⟩
        simp [f'] at eq
        split at eq
        case isTrue =>
          simp at eq
          have := Fin.val_eq_of_eq (h _ _ (Fin.eq_of_val_eq eq))
          simp at this
          exact absurd (this ▸ x.isLt) (Nat.lt_irrefl _)
        case isFalse nlt =>
          have := Fin.eq_of_not_lt nlt
          exact ⟨⟨x.val, Nat.lt_trans x.isLt (Nat.lt_succ_self n)⟩, this⟩
      else
        exact ⟨n', Fin.eq_of_not_lt isLt'⟩


end Regex.Data.SparseSet.Bijection
