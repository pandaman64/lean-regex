import Regex.Regex.Basic
import Lean

open Regex.Data (Anchor PerlClassKind PerlClass Class Classes)
open Regex NFA Node
open Lean Syntax Elab Term

set_option autoImplicit false

namespace Regex.Elab

-- A term representing a proof of `prop` given by letting kernel decide `prop`
-- using an `Decidable` instance `inst`.
private def mkDecidableProof (prop : Expr) (inst : Expr) : Expr :=
  let refl := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) (mkConst ``true)
  mkApp3 (mkConst ``of_decide_eq_true) prop inst refl

instance : ToExpr Regex where
  toTypeExpr := mkConst ``Regex
  toExpr re :=
    let nfa := toExpr re.nfa
    -- Construct a term representing `nfa.WellFormed` using a decidable instance.
    let wfType := Expr.app (mkConst ``NFA.WellFormed) nfa
    let wfInstance := Expr.app (mkConst ``NFA.decWellFormed) nfa
    let wf := mkDecidableProof wfType wfInstance
    let maxTag := toExpr re.maxTag
    let optimizationInfo := toExpr re.optimizationInfo
    mkApp5 (mkConst ``Regex.mk) nfa wf maxTag (mkConst ``false) optimizationInfo

/--
Macro for creating a regex at compile time.

Parses a string literal into a `Regex` object during Lean's elaboration phase.
This allows regex patterns to be checked at compile time rather than runtime,
catching syntax errors during compilation instead of at runtime.

Examples:
- `re! "a+b*c?"` creates a compiled regex matching that pattern
- `re! r"\d"` can be combined with raw string literals for easier escaping
-/
elab "re!" lit:str : term => do
  match Regex.parse lit.getString with
  | Except.ok re => return toExpr re
  | Except.error e => throwError s!"failed to parse regex: {e}"

end Regex.Elab
