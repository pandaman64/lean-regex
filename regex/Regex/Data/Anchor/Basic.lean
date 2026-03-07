module

import Regex.Data.String
public import Lean.ToExpr

open String (Pos)
open Regex.Data.String

public section

namespace Regex.Data

inductive Anchor where
  | start
  | eos
  | wordBoundary
  | nonWordBoundary
deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

def Anchor.test {s : String} (p : Pos s) (anchor : Anchor) : Bool :=
  match anchor with
  | .start => p == s.startPos
  | .eos => p == s.endPos
  | .wordBoundary => isAtWordBoundary p
  | .nonWordBoundary => isAtNonWordBoundary p

end Regex.Data

end
