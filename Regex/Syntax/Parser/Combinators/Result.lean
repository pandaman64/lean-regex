import Regex.Syntax.Parser.Combinators.Rel

set_option autoImplicit false

open String (Iterator)

namespace Regex.Syntax.Parser.Combinators

inductive Result (s : Bool) (it : Iterator) (ε α : Type) where
  | ok : α → (it' : Iterator) → Rel s it' it → Result s it ε α
  | error : ε → Result s it ε α
  | fatal : ε → Result s it ε α

namespace Result

abbrev LE (it : Iterator) (ε α : Type) := Result false it ε α

abbrev LT (it : Iterator) (ε α : Type) := Result true it ε α

@[inline]
def imp {s₁ s₂ : Bool} {it ε α} (h : s₂ → s₁) : Result s₁ it ε α → Result s₂ it ε α
  | .ok a it' h' => .ok a it' (h'.imp h)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def transOr {s₁ s₂ it it' ε α} (h : Rel s₂ it' it) : Result s₁ it' ε α → Result (s₁ || s₂) it ε α
  | .ok a it'' h' => .ok a it'' (Rel.transOr h' h)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def trans {s it it' ε α} (h : Rel s it it') : Result s it ε α → Result s it' ε α
  | .ok a it'' h' => .ok a it'' (Rel.trans h' h)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def cast {s₁ s₂ it ε α} (h : s₁ = s₂) (res : Result s₁ it ε α) : Result s₂ it ε α :=
  res.imp (by simp [h])

@[inline]
def weaken {s it ε α} (res : Result s it ε α) : Result false it ε α :=
  res.imp (by simp)

@[inline]
def toExcept {s it ε α} (res : Result s it ε α) : Except ε α :=
  match res with
  | .ok a _ _ => .ok a
  | .error e => .error e
  | .fatal e => .error e

@[inline]
def opt {s it ε α} : Result s it ε α → Result false it ε (Option α)
  | .ok a it' h => .ok (.some a) it' h.weaken
  | .error _ => .ok .none it (Nat.le_refl _)
  | .fatal e => .fatal e

@[inline]
def complete {s it ε α} (expectedEof : ε) : Result s it ε α → Result s it ε α
  | .ok a it' h =>
    if it'.atEnd then
      .ok a it' h
    else
      .error expectedEof
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def guard {s it ε α β} (f : α → Except ε β) : Result s it ε α → Result s it ε β
  | .ok a it' h =>
    match f a with
    | .ok b => .ok b it' h
    | .error e => .error e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def map' {s it ε α β} (f : α → (it' : Iterator) → Rel s it' it → β) : Result s it ε α → Result s it ε β
  | .ok a it' h => .ok (f a it' h) it' h
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def map {s it ε α β} (f : α → β) : Result s it ε α → Result s it ε β :=
  map' fun a _ _ => f a

@[inline]
def seq {s it ε α β} (mf : Result s it ε (α → β)) (mx : Unit → Result s it ε α) : Result s it ε β :=
  match mf with
  | .ok f _ _ =>
    match mx () with
    | .ok a it'' h' => .ok (f a) it'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def seqLeft {s it ε α β} (mx : Result s it ε α) (my : Unit → Result s it ε β) : Result s it ε α :=
  match mx with
  | .ok a _ _ =>
    match my () with
    | .ok _ it'' h' => .ok a it'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def seqRight {s it ε α β} (mx : Result s it ε α) (my : Unit → Result s it ε β) : Result s it ε β :=
  match mx with
  | .ok _ _ _ =>
    match my () with
    | .ok b it'' h' => .ok b it'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def hOrElse {s₁ s₂ it ε α} (mx : Result s₁ it ε α) (my : Unit → Result s₂ it ε α) : Result (s₁ && s₂) it ε α :=
  match mx with
  | .ok a it' h => .ok a it' (h.imp (by simp_all))
  | .error _ => (my ()).imp (by simp)
  | .fatal e => .fatal e

@[inline]
def orElse {s it ε α} : Result s it ε α → (Unit → Result s it ε α) → Result s it ε α
  | .ok a it' h, _ => .ok a it' h
  | .error _, b => b ()
  | .fatal e, _ => .fatal e

@[inline]
def throw {s it ε α} (e : ε) : Result s it ε α := .error e

@[inline]
def tryCatch {s it ε α} (mx : Result s it ε α) (handle : ε → Result s it ε α) : Result s it ε α :=
  match mx with
  | .ok a it' h => .ok a it' h
  | .error e => handle e
  | .fatal e => .fatal e

@[inline]
def bind' {s₁ s₂ it ε α β} (mx : Result s₁ it ε α) (f : α → (it' : Iterator) → Rel s₁ it' it → Result s₂ it' ε β) : Result (s₁ || s₂) it ε β :=
  match mx with
  | .ok a it' h => (f a it' h).transOr h |>.cast (Bool.or_comm _ _)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def bind {s it ε α β} (mx : Result s it ε α) (f : α → Result s it ε β) : Result s it ε β :=
  match mx with
  | .ok a _ _ => f a
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def pure {it ε α} (a : α) : LE it ε α := .ok a it (Nat.le_refl _)

@[inline]
instance {s it ε} : Functor (Result s it ε) where
  map := map

@[inline]
instance {s it ε} : Seq (Result s it ε) where
  seq := seq

@[inline]
instance {s it ε} : SeqLeft (Result s it ε) where
seqLeft := seqLeft

@[inline]
instance {s it ε} : SeqRight (Result s it ε) where
  seqRight := seqRight

@[inline]
instance {s₁ s₂ it ε α} : HOrElse (Result s₁ it ε α) (Result s₂ it ε α) (Result (s₁ && s₂) it ε α) where
  hOrElse := hOrElse

@[inline]
instance {s it ε α} : OrElse (Result s it ε α) where
  orElse := orElse

@[inline]
instance {s it ε} : MonadExceptOf ε (Result s it ε) where
  throw := throw
  tryCatch := tryCatch

@[inline]
instance {s it ε} : Bind (Result s it ε) where
  bind := bind

@[inline]
instance {it ε} : Pure (LE it ε) where
  pure := pure

@[inline]
instance {it ε} : Monad (LE it ε) where
  bind := bind

end Result

end Regex.Syntax.Parser.Combinators
