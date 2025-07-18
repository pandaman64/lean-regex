import Regex.Data.String
import Lean

namespace Regex.Data

inductive Anchor where
  | start
  | eos
  | wordBoundary
  | nonWordBoundary
deriving DecidableEq, Repr, Inhabited, Lean.ToExpr

open String.Iterator

def Anchor.test (it : String.Iterator) (anchor : Anchor) : Bool :=
  match anchor with
  | .start => it.pos = 0
  | .eos => it.atEnd
  | .wordBoundary => isAtWordBoundary it
  | .nonWordBoundary => isAtNonWordBoundary it

-- Tests
#guard Anchor.test "".mkIterator .wordBoundary == false
#guard Anchor.test "".mkIterator .nonWordBoundary == true
#guard Anchor.test "a".mkIterator .wordBoundary == true
#guard Anchor.test "a".mkIterator .nonWordBoundary == false
#guard Anchor.test "a".mkIterator.next .wordBoundary == true
#guard Anchor.test "a".mkIterator.next .nonWordBoundary == false

end Regex.Data
