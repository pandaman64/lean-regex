import Regex.Data.Expr
import RegexCorrectness.Data.Expr.Semantics.CaptureGroups

set_option autoImplicit false

open String (Iterator)

namespace Regex.Data

inductive Expr.Captures : Iterator → Iterator → CaptureGroups → Expr → Prop where
  | char {it l c r} (vf : it.ValidFor l (c :: r)) : Expr.Captures it it.next .empty (.char c)
  | sparse {it l c r cs} (vf : it.ValidFor l (c :: r)) (h : c ∈ cs) : Expr.Captures it it.next .empty (.classes cs)
  | epsilon {it} (v : it.Valid) : Expr.Captures it it .empty .epsilon
  | anchor {it anchor} (v : it.Valid) (h : anchor.test it) : Expr.Captures it it .empty (.anchor anchor)
  | group {it it' groups tag e} (cap : Expr.Captures it it' groups e) :
    Expr.Captures it it' (.group tag it.pos it'.pos groups) (.group tag e)
  | alternateLeft {it it' groups e₁ e₂} (cap : Expr.Captures it it' groups e₁) :
    Expr.Captures it it' groups (.alternate e₁ e₂)
  | alternateRight {it it' groups e₁ e₂} (cap : Expr.Captures it it' groups e₂) :
    Expr.Captures it it' groups (.alternate e₁ e₂)
  | concat {it it' it'' groups₁ groups₂ e₁ e₂} (cap₁ : Expr.Captures it it' groups₁ e₁) (cap₂ : Expr.Captures it' it'' groups₂ e₂) :
    Expr.Captures it it'' (.concat groups₁ groups₂) (.concat e₁ e₂)
  | starEpsilon {it e} (v : it.Valid) : Expr.Captures it it .empty (.star e)
  | starConcat {it it' it'' groups₁ groups₂ e} (cap₁ : Expr.Captures it it' groups₁ e) (cap₂ : Expr.Captures it' it'' groups₂ (.star e)) :
    Expr.Captures it it'' (.concat groups₁ groups₂) (.star e)

namespace Expr.Captures

theorem validL {it it' groups e} (c : Expr.Captures it it' groups e) : it.Valid := by
  induction c with
  | char vf => exact vf.valid
  | sparse vf => exact vf.valid
  | epsilon v => exact v
  | anchor v h => exact v
  | group _ ih => exact ih
  | alternateLeft _ ih => exact ih
  | alternateRight _ ih => exact ih
  | concat _ _ ih₁ => exact ih₁
  | starEpsilon v => exact v
  | starConcat _ _ ih₁ => exact ih₁

theorem validR {it it' groups e} (c : Expr.Captures it it' groups e) : it'.Valid := by
  induction c with
  | char vf => exact vf.next.valid
  | sparse vf => exact vf.next.valid
  | epsilon v => exact v
  | anchor v h => exact v
  | group _ ih => exact ih
  | alternateLeft _ ih => exact ih
  | alternateRight _ ih => exact ih
  | concat _ _ _ ih₂ => exact ih₂
  | starEpsilon v => exact v
  | starConcat _ _ _ ih₂ => exact ih₂

theorem toString_eq {it it' groups e} (c : Expr.Captures it it' groups e) : it'.toString = it.toString := by
  induction c with
  | char => simp [String.Iterator.next]
  | sparse => simp [String.Iterator.next]
  | epsilon v => rfl
  | anchor v h => rfl
  | group _ ih => exact ih
  | alternateLeft _ ih => exact ih
  | alternateRight _ ih => exact ih
  | concat _ _ ih₁ ih₂ => rw [ih₂, ih₁]
  | starEpsilon => rfl
  | starConcat _ _ ih₁ ih₂ => rw [ih₂, ih₁]

theorem le_pos {it it' groups e} (c : Expr.Captures it it' groups e) : it.pos ≤ it'.pos := by
  induction c with
  | char vf => simp [vf.next.pos, vf.pos]
  | sparse vf => simp [vf.next.pos, vf.pos]
  | epsilon => exact Nat.le_refl _
  | anchor => exact Nat.le_refl _
  | group _ ih => exact ih
  | alternateLeft _ ih => exact ih
  | alternateRight _ ih => exact ih
  | concat _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂
  | starEpsilon => exact Nat.le_refl _
  | starConcat _ _ ih₁ ih₂ => exact Nat.le_trans ih₁ ih₂

end Expr.Captures

end Regex.Data
