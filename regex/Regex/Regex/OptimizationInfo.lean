import Regex.Data.Expr
import Lean.ToExpr

open Regex.Data (Expr)
open String (Iterator)

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
  { firstChars := expr.firstChars (maxSize := 8) }

def findStart (self : OptimizationInfo) (it : Iterator) : Iterator :=
  match self.firstChars with
  | .some cs => it.find (cs.contains ·)
  | .none => it

end OptimizationInfo

end Regex
