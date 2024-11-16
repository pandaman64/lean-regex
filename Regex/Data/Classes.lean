def Char.MAX_UNICODE : Nat := 0x10FFFF

namespace Regex.Data

inductive PerlClassKind where
  | digit
  | space
  | word
deriving Repr

-- NOTE: we may want to interpret these as Unicode character properties in the future
def PerlClassKind.mem (c : Char) (kind : PerlClassKind) : Bool :=
  match kind with
  | PerlClassKind.digit => c.isDigit
  | PerlClassKind.space => c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == '\x0C'
  | PerlClassKind.word => c.isAlphanum

structure PerlClass where
  negated : Bool
  kind : PerlClassKind
deriving Repr

def PerlClass.mem (c : Char) (pc : PerlClass) : Bool :=
  if pc.negated then !pc.kind.mem c else pc.kind.mem c

-- NOTE: s ≤ e prevents this from deriving Repr :(
inductive Class where
  | single : Char → Class
  | range : (s : Char) → (e : Char) → s ≤ e → Class
  | perl : PerlClass → Class

instance : Repr Class where
  reprPrec cls _ :=
    match cls with
    | .single c => repr c
    | .range s e _ => s!"{repr s}-{repr e}"
    | .perl pc => repr pc

-- '.' matches any character except line break (\x0A)
def Class.beforeLineBreak : Class := Class.range (Char.ofNat 0) '\x09' (by decide)
def Class.afterLineBreak : Class := Class.range '\x0B' (Char.ofNat Char.MAX_UNICODE) (by decide)

def Class.mem (c : Char) : Class → Bool
  | Class.single c' => c == c'
  | Class.range s e _ => s ≤ c ∧ c ≤ e
  | Class.perl pc => pc.mem c

structure Classes where
  negated : Bool
  classes : Array Class
deriving Repr

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
