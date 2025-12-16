set_option autoImplicit false

open String (Pos)

namespace Regex.Syntax.Parser.Combinators

variable {s : String}

def Rel.LE (p' p : Pos s) : Prop := p ≤ p'

def Rel.LT (p' p : Pos s) : Prop := p < p'

def Rel (strict : Bool) : Pos s → Pos s → Prop :=
  if strict then Rel.LT else Rel.LE

namespace Rel

instance : Trans (@Rel.LE s) (@Rel.LE s) (@Rel.LE s) where
  trans h h' := Nat.le_trans h' h

instance : Trans (@Rel.LE s) (@Rel.LT s) (@Rel.LT s) where
  trans h h' := Nat.lt_of_lt_of_le h' h

instance : Trans (@Rel.LT s) (@Rel.LE s) (@Rel.LT s) where
  trans h h' := Nat.lt_of_le_of_lt h' h

instance : Trans (@Rel.LT s) (@Rel.LT s) (@Rel.LT s) where
  trans h h' := Nat.lt_trans h' h

def imp {strict₁ strict₂ : Bool} {p' p : Pos s} (h : strict₂ → strict₁) (rel : Rel strict₁ p' p) : Rel strict₂ p' p :=
  match strict₁, strict₂ with
  | false, false => rel
  | false, true => by simp at h
  | true, false => Nat.le_of_lt rel
  | true, true => rel

def weaken {strict : Bool} {p' p : Pos s} (rel : Rel strict p' p) : Rel false p' p :=
  rel.imp (by simp)

def transOr {strict₁ strict₂ : Bool} {p p' p'' : Pos s} (h : Rel strict₁ p p') (h' : Rel strict₂ p' p'') : Rel (strict₁ || strict₂) p p'' := by
  match strict₁, strict₂ with
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

def trans {strict : Bool} {p p' p'' : Pos s} (h : Rel strict p p') (h' : Rel strict p' p'') : Rel strict p p'' :=
  (Bool.or_self strict) ▸ transOr h h'

instance {strict₁ strict₂ : Bool} : Trans (@Rel s strict₁) (@Rel s strict₂) (@Rel s (strict₁ || strict₂)) where
  trans := transOr

instance {strict : Bool} : Trans (@Rel s strict) (@Rel s strict) (@Rel s strict) where
  trans := trans

end Rel

end Regex.Syntax.Parser.Combinators
