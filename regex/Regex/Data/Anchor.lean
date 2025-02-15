namespace Regex.Data

inductive Anchor where
  | start
  | eos
deriving DecidableEq, Repr, Inhabited

def Anchor.test (it : String.Iterator) (anchor : Anchor) : Bool :=
  match anchor with
  | Anchor.start => it.pos = 0
  | Anchor.eos => it.atEnd

end Regex.Data
