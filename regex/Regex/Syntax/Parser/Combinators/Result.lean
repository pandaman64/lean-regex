import Regex.Syntax.Parser.Combinators.Rel

set_option autoImplicit false

open String (ValidPos)

namespace Regex.Syntax.Parser.Combinators

variable {s : String}

inductive Result (strict : Bool) (p : ValidPos s) (ε α : Type) where
  | ok : α → (p' : ValidPos s) → Rel strict p' p → Result strict p ε α
  | error : ε → Result strict p ε α
  | fatal : ε → Result strict p ε α

namespace Result

abbrev LE (p : ValidPos s) (ε α : Type) := Result false p ε α

abbrev LT (p : ValidPos s) (ε α : Type) := Result true p ε α

@[inline]
def imp {strict₁ strict₂ : Bool} {p : ValidPos s} {ε α} (h : strict₂ → strict₁) : Result strict₁ p ε α → Result strict₂ p ε α
  | .ok a it' h' => .ok a it' (h'.imp h)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def transOr {strict₁ strict₂ : Bool} {p p' : ValidPos s} {ε α} (h : Rel strict₂ p' p) : Result strict₁ p' ε α → Result (strict₁ || strict₂) p ε α
  | .ok a it'' h' => .ok a it'' (Rel.transOr h' h)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def trans {strict : Bool} {p p' : ValidPos s} {ε α} (h : Rel strict p p') : Result strict p ε α → Result strict p' ε α
  | .ok a it'' h' => .ok a it'' (Rel.trans h' h)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def cast {strict₁ strict₂ : Bool} {p : ValidPos s} {ε α} (h : strict₁ = strict₂) (res : Result strict₁ p ε α) : Result strict₂ p ε α :=
  res.imp (by simp [h])

@[inline]
def weaken {strict : Bool} {p : ValidPos s} {ε α} (res : Result strict p ε α) : Result false p ε α :=
  res.imp (by simp)

@[inline]
def toExcept {strict : Bool} {p : ValidPos s} {ε α} (res : Result strict p ε α) : Except ε α :=
  match res with
  | .ok a _ _ => .ok a
  | .error e => .error e
  | .fatal e => .error e

@[inline]
def opt {strict : Bool} {p : ValidPos s} {ε α} : Result strict p ε α → Result false p ε (Option α)
  | .ok a p' h => .ok (.some a) p' h.weaken
  | .error _ => .ok .none p (Nat.le_refl _)
  | .fatal e => .fatal e

@[inline]
def complete {strict : Bool} {p : ValidPos s} {ε α} (expectedEof : ε) : Result strict p ε α → Result strict p ε α
  | .ok a p' h =>
    if p' == s.endValidPos then
      .ok a p' h
    else
      .error expectedEof
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def commit {strict : Bool} {p : ValidPos s} {ε α} : Result strict p ε α → Result strict p ε α
  | .ok a p' h => .ok a p' h
  | .error e => .fatal e
  | .fatal e => .fatal e

@[inline]
def guard {strict : Bool} {p : ValidPos s} {ε α β} (f : α → Except ε β) : Result strict p ε α → Result strict p ε β
  | .ok a p' h =>
    match f a with
    | .ok b => .ok b p' h
    | .error e => .error e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def map' {strict : Bool} {p : ValidPos s} {ε α β} (f : α → (p' : ValidPos s) → Rel strict p' p → β) : Result strict p ε α → Result strict p ε β
  | .ok a p' h => .ok (f a p' h) p' h
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def map {strict : Bool} {p : ValidPos s} {ε α β} (f : α → β) : Result strict p ε α → Result strict p ε β :=
  map' fun a _ _ => f a

@[inline]
def seq {strict : Bool} {p : ValidPos s} {ε α β} (mf : Result strict p ε (α → β)) (mx : Unit → Result strict p ε α) : Result strict p ε β :=
  match mf with
  | .ok f _ _ =>
    match mx () with
    | .ok a p'' h' => .ok (f a) p'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def seqLeft {strict : Bool} {p : ValidPos s} {ε α β} (mx : Result strict p ε α) (my : Unit → Result strict p ε β) : Result strict p ε α :=
  match mx with
  | .ok a _ _ =>
    match my () with
    | .ok _ p'' h' => .ok a p'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def seqRight {strict : Bool} {p : ValidPos s} {ε α β} (mx : Result strict p ε α) (my : Unit → Result strict p ε β) : Result strict p ε β :=
  match mx with
  | .ok _ _ _ =>
    match my () with
    | .ok b p'' h' => .ok b p'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def hOrElse {strict₁ strict₂ : Bool} {p : ValidPos s} {ε α} (mx : Result strict₁ p ε α) (my : Unit → Result strict₂ p ε α) : Result (strict₁ && strict₂) p ε α :=
  match mx with
  | .ok a p' h => .ok a p' (h.imp (by simp_all))
  | .error _ => (my ()).imp (by simp)
  | .fatal e => .fatal e

@[inline]
def orElse {strict : Bool} {p : ValidPos s} {ε α} : Result strict p ε α → (Unit → Result strict p ε α) → Result strict p ε α
  | .ok a p' h, _ => .ok a p' h
  | .error _, b => b ()
  | .fatal e, _ => .fatal e

@[inline]
def throw {strict : Bool} {p : ValidPos s} {ε α} (e : ε) : Result strict p ε α := .error e

@[inline]
def tryCatch {strict : Bool} {p : ValidPos s} {ε α} (mx : Result strict p ε α) (handle : ε → Result strict p ε α) : Result strict p ε α :=
  match mx with
  | .ok a p' h => .ok a p' h
  | .error e => handle e
  | .fatal e => .fatal e

@[inline]
def bind' {strict₁ strict₂ : Bool} {p : ValidPos s} {ε α β} (mx : Result strict₁ p ε α) (f : α → (p' : ValidPos s) → Rel strict₁ p' p → Result strict₂ p' ε β) : Result (strict₁ || strict₂) p ε β :=
  match mx with
  | .ok a p' h => (f a p' h).transOr h |>.cast (Bool.or_comm _ _)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def bind {strict : Bool} {p : ValidPos s} {ε α β} (mx : Result strict p ε α) (f : α → Result strict p ε β) : Result strict p ε β :=
  match mx with
  | .ok a _ _ => f a
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def pure {p : ValidPos s} {ε α} (a : α) : LE p ε α := .ok a p (Nat.le_refl _)

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε} : Functor (Result strict p ε) where
  map := map

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε} : Seq (Result strict p ε) where
  seq := seq

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε} : SeqLeft (Result strict p ε) where
seqLeft := seqLeft

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε} : SeqRight (Result strict p ε) where
  seqRight := seqRight

@[inline]
instance {strict₁ strict₂ : Bool} {p : ValidPos s} {ε α} : HOrElse (Result strict₁ p ε α) (Result strict₂ p ε α) (Result (strict₁ && strict₂) p ε α) where
  hOrElse := hOrElse

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε α} : OrElse (Result strict p ε α) where
  orElse := orElse

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε} : MonadExceptOf ε (Result strict p ε) where
  throw := throw
  tryCatch := tryCatch

@[inline]
instance {strict : Bool} {p : ValidPos s} {ε} : Bind (Result strict p ε) where
  bind := bind

@[inline]
instance {p : ValidPos s} {ε} : Pure (LE p ε) where
  pure := pure

@[inline]
instance {p : ValidPos s} {ε} : Monad (LE p ε) where
  bind := bind

end Result

end Regex.Syntax.Parser.Combinators
