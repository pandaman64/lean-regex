set_option autoImplicit false

open String (Iterator)

namespace Regex.Syntax.Parser.Combinators

def Rel.LE (it' it : Iterator) : Prop := it'.remainingBytes ≤ it.remainingBytes

def Rel.LT (it' it : Iterator) : Prop := it'.remainingBytes < it.remainingBytes

def Rel (s : Bool) : Iterator → Iterator → Prop :=
  if s then Rel.LT else Rel.LE

namespace Rel

instance : Trans Rel.LE Rel.LE Rel.LE where
  trans h h' := Nat.le_trans h h'

instance : Trans Rel.LE Rel.LT Rel.LT where
  trans h h' := Nat.lt_of_le_of_lt h h'

instance : Trans Rel.LT Rel.LE Rel.LT where
  trans h h' := Nat.lt_of_lt_of_le h h'

instance : Trans Rel.LT Rel.LT Rel.LT where
  trans h h' := Nat.lt_trans h h'

def imp {s₁ s₂ : Bool} {it' it} (h : s₂ → s₁) (rel : Rel s₁ it' it) : Rel s₂ it' it :=
  match s₁, s₂ with
  | false, false => rel
  | false, true => by simp at h
  | true, false => Nat.le_of_lt rel
  | true, true => rel

def weaken {s it' it} (rel : Rel s it' it) : Rel false it' it :=
  rel.imp (by simp)

def transOr {s₁ s₂ it it' it''} (h : Rel s₁ it it') (h' : Rel s₂ it' it'') : Rel (s₁ || s₂) it it'' := by
  match s₁, s₂ with
  | false, false =>
    simp [Rel] at *
    exact Trans.trans h h'
  | false, true =>
    simp [Rel] at *
    exact Trans.trans h h'
  | true, false =>
    simp [Rel] at *
    exact Trans.trans h h'
  | true, true =>
    simp [Rel] at *
    exact Trans.trans h h'

def trans {s it it' it''} (h : Rel s it it') (h' : Rel s it' it'') : Rel s it it'' :=
  (Bool.or_self s) ▸ transOr h h'

instance {s₁ s₂} : Trans (Rel s₁) (Rel s₂) (Rel (s₁ || s₂)) where
  trans := transOr

instance {s} : Trans (Rel s) (Rel s) (Rel s) where
  trans := trans

end Rel

end Regex.Syntax.Parser.Combinators
