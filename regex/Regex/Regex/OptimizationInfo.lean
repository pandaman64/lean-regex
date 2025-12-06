import Regex.Data.Expr
import Regex.Data.String
import Lean.ToExpr

open Regex.Data (Expr)
open String (ValidPos)

namespace Regex

structure OptimizationInfo where
  /--
  When `firstChars` is `.some chars`, all matching strings must start with one of the characters in `chars`.

  The regex engine will optimize the search to skip positions that do not start with any character in `chars`.
  -/
  firstChars : Option (Array Char)
deriving Repr, Inhabited, DecidableEq, Lean.ToExpr

namespace OptimizationInfo

def fromExpr (expr : Expr) : OptimizationInfo :=
  { firstChars := expr.firstChars (maxSize := 8) |>.map Std.HashSet.toArray }

def findStart {s : String} (self : OptimizationInfo) (pos : ValidPos s) : ValidPos s :=
  match self.firstChars with
  | .some cs => pos.find (cs.contains ·)
  | .none => pos

end OptimizationInfo

end Regex
