import Regex.Data.String
import Lean

open String (Pos)
open Regex.Data.String

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

-- Tests
#guard Anchor.test "".startPos .wordBoundary == false
#guard Anchor.test "".startPos .nonWordBoundary == true
#guard Anchor.test "a".startPos .wordBoundary == true
#guard Anchor.test "a".startPos .nonWordBoundary == false
#guard Anchor.test ("a".startPos.next (by decide)) .wordBoundary == true
#guard Anchor.test ("a".startPos.next (by decide)) .nonWordBoundary == false

end Regex.Data
