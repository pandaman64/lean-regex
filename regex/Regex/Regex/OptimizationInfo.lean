import Regex.Data.Expr
import Lean.ToExpr

open Regex.Data (Expr)
open String (Iterator)

namespace Regex

structure OptimizationInfo where
  /--
  When `firstChar` is `.some c`, all matching strings must start with `c`.

  The regex engine will optimize the search to skip positions that do not start with `c`.
  -/
  firstChar : Option Char
deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

namespace OptimizationInfo

def fromExpr (expr : Expr) : OptimizationInfo :=
  { firstChar := expr.firstChar }

def findStart (self : OptimizationInfo) (it : Iterator) : Iterator :=
  if let .some c := self.firstChar then
    it.find (· = c)
  else
    it

end OptimizationInfo

end Regex
