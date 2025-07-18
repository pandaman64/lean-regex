import Lean

def Char.MAX_UNICODE : Nat := 0x10FFFF

namespace Regex.Data

inductive PerlClassKind where
  | digit
  | space
  | word
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

-- NOTE: we may want to interpret these as Unicode character properties in the future
def PerlClassKind.mem (c : Char) (kind : PerlClassKind) : Bool :=
  match kind with
  | PerlClassKind.digit => c.isDigit
  | PerlClassKind.space => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'
  | PerlClassKind.word => c.isAlphanum || c == '_'

structure PerlClass where
  negated : Bool
  kind : PerlClassKind
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

def PerlClass.mem (c : Char) (pc : PerlClass) : Bool :=
  if pc.negated then !pc.kind.mem c else pc.kind.mem c

inductive Class where
  | single : Char → Class
  | range : (s : Char) → (e : Char) → Class
  | perl : PerlClass → Class
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

-- '.' matches any character except line break (\x0A)
def Class.beforeLineBreak : Class := Class.range (Char.ofNat 0) '\x09'
def Class.afterLineBreak : Class := Class.range '\x0B' (Char.ofNat Char.MAX_UNICODE)

def Class.mem (c : Char) : Class → Bool
  | Class.single c' => c == c'
  | Class.range s e => s ≤ c ∧ c ≤ e
  | Class.perl pc => pc.mem c

structure Classes where
  negated : Bool
  classes : Array Class
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

def Classes.mem (c : Char) (cs : Classes) : Bool :=
  if cs.negated then
    cs.classes.all (fun cls => !cls.mem c)
  else
    cs.classes.any (fun cls => cls.mem c)

instance : Membership Char Classes where
  mem cs c := cs.mem c

theorem Classes.mem_mem {c : Char} {cs : Classes} : c ∈ cs ↔ cs.mem c := Iff.rfl

@[inline]
instance {c : Char} {cs : Classes} : Decidable (c ∈ cs) :=
  match h : cs.mem c with
  | true => isTrue h
  | false => isFalse (by simp [Classes.mem_mem, h])

end Regex.Data
