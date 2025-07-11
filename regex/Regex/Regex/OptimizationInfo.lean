import Regex.Data.Expr

open Regex.Data (Expr)

namespace Regex

structure OptimizationInfo where
  /--
  When `firstChar` is `.some c`, all matching strings must start with `c`.

  The regex engine will optimize the search to skip positions that do not start with `c`.
  -/
  firstChar : Option Char
deriving Repr, Inhabited, DecidableEq

namespace OptimizationInfo

def fromExpr (expr : Expr) : OptimizationInfo :=
  { firstChar := expr.firstChar }

end OptimizationInfo

end Regex
