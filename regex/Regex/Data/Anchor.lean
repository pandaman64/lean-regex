import Regex.Data.String
import Lean

open String (ValidPos)

namespace Regex.Data

inductive Anchor where
  | start
  | eos
  | wordBoundary
  | nonWordBoundary
deriving DecidableEq, Repr, Inhabited, Lean.ToExpr


def Anchor.test {s : String} (p : ValidPos s) (anchor : Anchor) : Bool :=
  match anchor with
  | .start => p == s.startValidPos
  | .eos => p == s.endValidPos
  | .wordBoundary => p.isAtWordBoundary
  | .nonWordBoundary => p.isAtNonWordBoundary

-- Tests
#guard Anchor.test "".startValidPos .wordBoundary == false
#guard Anchor.test "".startValidPos .nonWordBoundary == true
#guard Anchor.test "a".startValidPos .wordBoundary == true
#guard Anchor.test "a".startValidPos .nonWordBoundary == false
#guard Anchor.test ("a".startValidPos.next (by decide)) .wordBoundary == true
#guard Anchor.test ("a".startValidPos.next (by decide)) .nonWordBoundary == false

end Regex.Data
