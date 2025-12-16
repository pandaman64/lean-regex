import Regex.Syntax.Parser.Combinators.Result

set_option autoImplicit false

open String (Pos)

namespace Regex.Syntax.Parser.Combinators

/--
Total parser combinators a la [idris2-parser](https://github.com/stefan-hoeck/idris2-parser/tree/main).

`s` controls whether the input is strictly decreasing.
-/
abbrev Parser (s strict ε α) := ∀ (p : Pos s), Result strict p ε α

namespace Parser

abbrev LE (s ε α) := Parser s false ε α

abbrev LT (s ε α) := Parser s true ε α

@[inline]
def imp {s : String} {strict₁ strict₂ : Bool} {ε α} (h : strict₂ → strict₁) : Parser s strict₁ ε α → Parser s strict₂ ε α
  | p, pos => (p pos).imp h

@[inline]
def weaken {s strict ε α} : Parser s strict ε α → Parser s false ε α
  | p, pos => (p pos).weaken

@[inline]
def cast {s : String} {strict₁ strict₂ : Bool} {ε α} (h : strict₁ = strict₂) : Parser s strict₁ ε α → Parser s strict₂ ε α
  | p, pos => (p pos).cast h

@[inline]
def opt {s strict ε α} : Parser s strict ε α → Parser s false ε (Option α)
  | p, pos => (p pos).opt

@[inline]
def guard {s strict ε α β} (f : α → Except ε β) : Parser s strict ε α → Parser s strict ε β
  | p, pos => (p pos).guard f

@[inline]
def complete {s strict ε α} (expectedEof : ε) : Parser s strict ε α → Parser s strict ε α
  | p, pos => (p pos).complete expectedEof

@[inline]
def debug {s strict ε α} [ToString α] (name : String) (p : Parser s strict ε α) : Parser s strict ε α
  | pos => dbgTrace s!"Parsing {name} at ({s}, {pos.offset})" fun () =>
    (p pos).map (fun a => dbgTrace s!"parsed {a}" (fun () => a))

@[inline]
def commit {s strict ε α} : Parser s strict ε α → Parser s strict ε α
  | p, pos => (p pos).commit

@[inline]
def map {s strict ε α β} (f : α → β) : Parser s strict ε α → Parser s strict ε β
  | p, pos => (p pos).map f

@[inline]
def mapConst {s strict ε α β} (a : α) : Parser s strict ε β → Parser s strict ε α
  | p, pos => Functor.mapConst a (p pos)

@[inline]
def seq {s strict ε α β} (p : Parser s strict ε (α → β)) (q : Unit → Parser s strict ε α) : Parser s strict ε β
  | pos =>
    match p pos with
    | .ok f pos' h => (q () pos').trans h |>.map f
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def seqLeft {s strict ε α β} (p : Parser s strict ε α) (q : Unit → Parser s strict ε β) : Parser s strict ε α
  | pos =>
    match p pos with
    | .ok a pos' h => (q () pos').trans h |>.map (fun _ => a)
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def seqRight {s strict ε α β} (p : Parser s strict ε α) (q : Unit → Parser s strict ε β) : Parser s strict ε β
  | pos =>
    match p pos with
    | .ok _ pos' h => (q () pos').trans h
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def hOrElse {s strict₁ strict₂ ε α} (p : Parser s strict₁ ε α) (q : Unit → Parser s strict₂ ε α) : Parser s (strict₁ && strict₂) ε α
  | pos =>
    match p pos with
    | .ok a pos' h => .ok a pos' (h.imp (by simp_all))
    | .error _ => (q () pos).imp (by simp)
    | .fatal e => .fatal e

@[inline]
def orElse {s strict ε α} (p : Parser s strict ε α) (q : Unit → Parser s strict ε α) : Parser s strict ε α
  | pos =>
    match p pos with
    | .ok a pos' h => .ok a pos' h
    | .error _ => q () pos
    | .fatal e => .fatal e

@[inline]
def throw {s strict ε α} (e : ε) : Parser s strict ε α := fun _ => .error e

@[inline]
def tryCatch {s strict ε α} (p : Parser s strict ε α) (handle : ε → Parser s strict ε α) : Parser s strict ε α
  | pos =>
    match p pos with
    | .ok a pos' h => .ok a pos' h
    | .error e => handle e pos
    | .fatal e => .fatal e

@[inline]
def bindOr {s strict₁ strict₂ ε α β} (p : Parser s strict₁ ε α) (f : α → Parser s strict₂ ε β) : Parser s (strict₁ || strict₂) ε β
  | pos =>
    match p pos with
    | .ok a pos' h => ((f a pos').transOr h).cast (by grind)
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def bind {s strict ε α β} (p : Parser s strict ε α) (f : α → Parser s strict ε β) : Parser s strict ε β
  | pos =>
    match p pos with
    | .ok a pos' h => (f a pos').trans h
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def pure {s ε α} (a : α) : Parser s false ε α
  | pos => .ok a pos (Nat.le_refl _)

@[inline]
instance {s strict ε} : Functor (Parser s strict ε) where
  map := map

@[inline]
instance {s strict ε} : Seq (Parser s strict ε) where
  seq := seq

@[inline]
instance {s strict ε} : SeqLeft (Parser s strict ε) where
  seqLeft := seqLeft

@[inline]
instance {s strict ε} : SeqRight (Parser s strict ε) where
  seqRight := seqRight

@[inline]
instance {s strict₁ strict₂ ε α} : HOrElse (Parser s strict₁ ε α) (Parser s strict₂ ε α) (Parser s (strict₁ && strict₂) ε α) where
  hOrElse := hOrElse

@[inline]
instance {s strict ε α} : OrElse (Parser s strict ε α) where
  orElse := orElse

@[inline]
instance {s strict ε} : MonadExceptOf ε (Parser s strict ε) where
  throw := throw
  tryCatch := tryCatch

@[inline]
instance {s strict ε} : Bind (Parser s strict ε) where
  bind := bind

@[inline]
instance {s ε} : Pure (Parser s false ε) where
  pure := pure

@[inline]
instance {s ε} : Monad (Parser s false ε) where
  bind := bind

end Parser

end Regex.Syntax.Parser.Combinators
