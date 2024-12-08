import Regex.Regex.Basic
import Lean

open Regex.Data (PerlClassKind PerlClass Class Classes)
open Regex NFA Node
open Lean Syntax Elab Term

set_option autoImplicit false

namespace Regex.Elab

-- A term representing a proof of `prop` given by letting kernel decide `prop`
-- using an `Decidable` instance `inst`.
private def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

instance : ToExpr PerlClassKind where
  toTypeExpr := mkConst ``PerlClassKind
  toExpr
    | .digit => mkConst ``PerlClassKind.digit
    | .space => mkConst ``PerlClassKind.space
    | .word => mkConst ``PerlClassKind.word

instance : ToExpr PerlClass where
  toTypeExpr := mkConst ``PerlClass
  toExpr pc := mkApp2 (mkConst ``PerlClass.mk) (toExpr pc.negated) (toExpr pc.kind)

instance : ToExpr Class where
  toTypeExpr := mkConst ``Class
  toExpr
    | .single c => .app (mkConst ``Class.single) (toExpr c)
    | .range s e _ =>
      let s := toExpr s
      let e := toExpr e
      -- Construct a term representing `s ≤ e` using a decidable instance.
      let leType := mkApp4 (mkConst ``LE.le [0]) (mkConst ``Char) (mkConst ``Char.instLE) s e
      let leInstance := mkApp2 (mkConst ``Char.instDecidableLe) s e
      let le := mkDecidableProof leType leInstance

      mkApp3 (mkConst ``Class.range) s e le
    | .perl pc => toExpr pc

instance : ToExpr Classes where
  toTypeExpr := mkConst ``Classes
  toExpr cs := mkApp2 (mkConst ``Classes.mk) (toExpr cs.negated) (toExpr cs.classes)

instance : ToExpr Node where
  toTypeExpr := mkConst ``Node
  toExpr
    | .done => mkConst ``Node.done
    | .fail => mkConst ``Node.fail
    | .epsilon next => .app (mkConst ``Node.epsilon) (toExpr next)
    | .char c next => mkApp2 (mkConst ``Node.char) (toExpr c) (toExpr next)
    | .sparse cs next => mkApp2 (mkConst ``Node.sparse) (toExpr cs) (toExpr next)
    | .split next₁ next₂ => mkApp2 (mkConst ``Node.split) (toExpr next₁) (toExpr next₂)
    | .save tag next => mkApp2 (mkConst ``Node.save) (toExpr tag) (toExpr next)

instance : ToExpr NFA where
  toTypeExpr := mkConst ``NFA
  toExpr nfa := mkApp2 (mkConst ``NFA.mk) (toExpr nfa.nodes) (toExpr nfa.start)

instance : ToExpr Regex where
  toTypeExpr := mkConst ``Regex
  toExpr re :=
    let nfa := toExpr re.nfa
    -- Construct a term representing `nfa.WellFormed` using a decidable instance.
    let wfType := Expr.app (mkConst ``NFA.WellFormed) nfa
    let wfInstance := Expr.app (mkConst ``NFA.decWellFormed) nfa
    let wf := mkDecidableProof wfType wfInstance
    let maxTag := toExpr re.maxTag
    mkApp3 (mkConst ``Regex.mk) nfa wf maxTag

elab "re!" lit:str : term => do
  match Regex.parse lit.getString with
  | Except.ok re => return toExpr re
  | Except.error e => throwError s!"failed to parse regex: {e}"

end Regex.Elab
