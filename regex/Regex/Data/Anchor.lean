namespace Regex.Data

inductive Anchor where
  | start
  | eos
  | wordBoundary
  | nonWordBoundary
deriving DecidableEq, Repr, Inhabited


namespace Iterator

def isWordChar (ch : Char) : Bool :=
  ch.isAlphanum || ch = '_'

def isCurrWord (it : String.Iterator) : Bool :=
  it.hasNext && isWordChar it.curr

def isPrevWord (it : String.Iterator) : Bool :=
  it.hasPrev && isWordChar it.prev.curr

def isAtWordBoundary (it : String.Iterator) : Bool :=
  isCurrWord it != isPrevWord it

def isAtNonWordBoundary (it : String.Iterator) : Bool :=
  isCurrWord it == isPrevWord it

end Iterator

def Anchor.test (it : String.Iterator) (anchor : Anchor) : Bool :=
  match anchor with
  | Anchor.start => it.pos = 0
  | Anchor.eos => it.atEnd
  | Anchor.wordBoundary => Iterator.isAtWordBoundary it
  | Anchor.nonWordBoundary => Iterator.isAtNonWordBoundary it

-- Tests
#guard Anchor.test "".mkIterator Anchor.wordBoundary == false
#guard Anchor.test "".mkIterator Anchor.nonWordBoundary == true
#guard Anchor.test "a".mkIterator Anchor.wordBoundary == true
#guard Anchor.test "a".mkIterator Anchor.nonWordBoundary == false
#guard Anchor.test "a".mkIterator.next Anchor.wordBoundary == true
#guard Anchor.test "a".mkIterator.next Anchor.nonWordBoundary == false

end Regex.Data
