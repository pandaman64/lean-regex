-- Minimal theory about the bijection between `Fin n`.
module
set_option autoImplicit false

namespace Regex.Data.SparseSet.Bijection

open Function (Injective Surjective)

public theorem surj_of_inj {n} (f : Fin n → Fin n) (h : Injective f) : Surjective f := by
  induction n with
  | zero =>
    intro y
    exact y.elim0
  | succ n ih =>
    let n' : Fin (n + 1) := ⟨n, Nat.lt_succ_self n⟩
    let f' (x : Fin n) : Fin n :=
      let x' : Fin (n + 1) := ⟨x.val, by grind⟩
      let y := f x'
      if isLt : y.val < n then
        ⟨y.val, isLt⟩
      else
        ⟨f ⟨n, by grind⟩, by grind⟩
    have inj' : Injective f' := by
      intro x y eq
      grind
    have surj' : Surjective f' := ih f' inj'

    intro y
    cases Nat.lt_or_eq_of_le y.isLt with
    | inl isLt => grind [surj' ⟨y.val, by grind⟩]
    | inr eq =>
      if isLt' : f n' < n then
        grind [surj' ⟨(f n').val, isLt'⟩]
      else
        grind

end Regex.Data.SparseSet.Bijection
