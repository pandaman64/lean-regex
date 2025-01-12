import Regex.Syntax.Parser.Combinators.Result

set_option autoImplicit false

open String (Iterator)

namespace Regex.Syntax.Parser.Combinators

/--
Total parser combinators a la [idris2-parser](https://github.com/stefan-hoeck/idris2-parser/tree/main).

`s` controls whether the input is strictly decreasing.
-/
abbrev Parser (s ε α) := ∀ (it : Iterator), Result s it ε α

namespace Parser

abbrev LE (ε α) := Parser false ε α

abbrev LT (ε α) := Parser true ε α

@[inline]
def imp {s₁ s₂ : Bool} {ε α} (h : s₂ → s₁) : Parser s₁ ε α → Parser s₂ ε α
  | p, it => (p it).imp h

@[inline]
def weaken {s ε α} : Parser s ε α → Parser false ε α
  | p, it => (p it).weaken

@[inline]
def cast {s₁ s₂ ε α} (h : s₁ = s₂) : Parser s₁ ε α → Parser s₂ ε α
  | p, it => (p it).cast h

@[inline]
def opt {s ε α} : Parser s ε α → Parser false ε (Option α)
  | p, it => (p it).opt

@[inline]
def guard {s ε α β} (f : α → Except ε β) : Parser s ε α → Parser s ε β
  | p, it => (p it).guard f

@[inline]
def complete {s ε α} (expectedEof : ε) : Parser s ε α → Parser s ε α
  | p, it => (p it).complete expectedEof

@[inline]
def debug {s ε α} [ToString α] (name : String) (p : Parser s ε α) : Parser s ε α
  | it => dbgTrace s!"Parsing {name} at {it}" fun () =>
    (p it).map (fun a => dbgTrace s!"parsed {a}" (fun () => a))

@[inline]
def map {s ε α β} (f : α → β) : Parser s ε α → Parser s ε β
  | p, it => (p it).map f

@[inline]
def mapConst {s ε α β} (a : α) : Parser s ε β → Parser s ε α
  | p, it => Functor.mapConst a (p it)

@[inline]
def seq {s ε α β} (p : Parser s ε (α → β)) (q : Unit → Parser s ε α) : Parser s ε β
  | it =>
    match p it with
    | .ok f it' h => (q () it').trans h |>.map f
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def seqLeft {s ε α β} (p : Parser s ε α) (q : Unit → Parser s ε β) : Parser s ε α
  | it =>
    match p it with
    | .ok a it' h => (q () it').trans h |>.map (fun _ => a)
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def seqRight {s ε α β} (p : Parser s ε α) (q : Unit → Parser s ε β) : Parser s ε β
  | it =>
    match p it with
    | .ok _ it' h => (q () it').trans h
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def hOrElse {s₁ s₂ ε α} (p : Parser s₁ ε α) (q : Unit → Parser s₂ ε α) : Parser (s₁ && s₂) ε α
  | it =>
    match p it with
    | .ok a it' h => .ok a it' (h.imp (by simp_all))
    | .error _ => (q () it).imp (by simp)
    | .fatal e => .fatal e

@[inline]
def orElse {s ε α} (p : Parser s ε α) (q : Unit → Parser s ε α) : Parser s ε α
  | it =>
    match p it with
    | .ok a it' h => .ok a it' h
    | .error _ => q () it
    | .fatal e => .fatal e

@[inline]
def throw {s ε α} (e : ε) : Parser s ε α := fun _ => .error e

@[inline]
def tryCatch {s ε α} (p : Parser s ε α) (handle : ε → Parser s ε α) : Parser s ε α
  | it =>
    match p it with
    | .ok a it' h => .ok a it' h
    | .error e => handle e it
    | .fatal e => .fatal e

@[inline]
def bindOr {s₁ s₂ ε α β} (p : Parser s₁ ε α) (f : α → Parser s₂ ε β) : Parser (s₂ || s₁) ε β
  | it =>
    match p it with
    | .ok a it' h => (f a it').transOr h
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def bind {s ε α β} (p : Parser s ε α) (f : α → Parser s ε β) : Parser s ε β
  | it =>
    match p it with
    | .ok a it' h => (f a it').trans h
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def pure {ε α} (a : α) : Parser false ε α
  | it => .ok a it (Nat.le_refl _)

@[inline]
instance {s ε} : Functor (Parser s ε) where
  map := map

@[inline]
instance {s ε} : Seq (Parser s ε) where
  seq := seq

@[inline]
instance {s ε} : SeqLeft (Parser s ε) where
  seqLeft := seqLeft

@[inline]
instance {s ε} : SeqRight (Parser s ε) where
  seqRight := seqRight

@[inline]
instance {s₁ s₂ ε α} : HOrElse (Parser s₁ ε α) (Parser s₂ ε α) (Parser (s₁ && s₂) ε α) where
  hOrElse := hOrElse

@[inline]
instance {s ε α} : OrElse (Parser s ε α) where
  orElse := orElse

@[inline]
instance {s ε} : MonadExceptOf ε (Parser s ε) where
  throw := throw
  tryCatch := tryCatch

@[inline]
instance {s ε} : Bind (Parser s ε) where
  bind := bind

@[inline]
instance {ε} : Pure (Parser false ε) where
  pure := pure

@[inline]
instance {ε} : Monad (Parser false ε) where
  bind := bind

end Parser

end Regex.Syntax.Parser.Combinators
