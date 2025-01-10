import Batteries.Data.String

set_option autoImplicit false

open String (Iterator)

namespace String.Iterator

@[simp]
theorem next'_eq {it : Iterator} (h : it.hasNext) : it.next' h = it.next := rfl

@[simp]
theorem next_remainingBytes_lt {it : Iterator} (h : it.hasNext) : it.next.remainingBytes < it.remainingBytes := by
  simp [remainingBytes, hasNext, next, String.next] at *
  have : (it.s.get it.i).utf8Size > 0 := Char.utf8Size_pos _
  omega

end String.Iterator

namespace TParser

universe u v

inductive Result (ε : Type u) (α : Type v) where
  /--
  Parser succeeded with a value and the iterator moved forward.
  -/
  | ok (val : α) : Result ε α
  /--
  Parser failed with a recoverable error.
  -/
  | error (e : ε) : Result ε α
  /--
  Parser failed with an unrecoverable error.
  -/
  | fatal (e : ε) : Result ε α
deriving Repr

namespace Result

@[inline]
def commit {ε α} (res : Result ε α) : Result ε α :=
  match res with
  | .ok v  => .ok v
  | .error e => .fatal e
  | .fatal e => .fatal e

@[inline]
def pure {ε α} (val : α) : Result ε α :=
  .ok val

@[inline]
def map {ε α β} (f : α → β) (res : Result ε α) : Result ε β :=
  match res with
  | .ok v => .ok (f v)
  | .error e => .error e
  | .fatal e => .fatal e

@[inline]
def bind {ε α β} (res : Result ε α) (f : α → Result ε β) : Result ε β :=
  match res with
  | .ok v => f v
  | .error e => .error e
  | .fatal e => .fatal e

/--
Catch a recoverable error with a handler. A fatal error cannot be caught.
-/
@[inline]
def tryCatch {ε α} (ma : Result ε α) (handle : ε → Result ε α) : Result ε α :=
  match ma with
  | .ok a => .ok a
  | .error e => handle e
  | .fatal e => .fatal e

def orElse {ε α} (x : Result ε α) (y : Unit → Result ε α) : Result ε α :=
  match x with
  | .ok a => .ok a
  | .error _ => y ()
  | .fatal e => .fatal e

@[inline]
instance {ε} : Monad (Result ε) where
  pure := Result.pure
  bind := Result.bind
  map := Result.map

@[inline]
instance {ε} : MonadExcept ε (Result ε) where
  throw := Result.error
  tryCatch := Result.tryCatch

@[inline]
instance {ε} [Inhabited ε] : Alternative (Result ε) where
  -- Is this the right choice?
  failure := .error default
  orElse := Result.orElse

@[inline]
instance {ε α} : OrElse (Result ε α) where
  orElse := Result.orElse

end Result

def ResultT (ε : Type u) (m : Type u → Type v) (α : Type u) : Type v :=
  m (Result ε α)

@[inline]
def ResultT.mk {ε : Type u} {m : Type u → Type v} {α : Type u} (x : m (Result ε α)) : ResultT ε m α := x

@[inline]
def ResultT.run {ε : Type u} {m : Type u → Type v} {α : Type u} (x : ResultT ε m α) : m (Result ε α) := x

namespace ResultT

variable {ε : Type u} {m : Type u → Type v} [Monad m]

@[inline]
def pure {α : Type u} (a : α) : ResultT ε m α :=
  .mk (Pure.pure (Result.ok a))

@[inline]
def bindCont {α β : Type u} (f : α → ResultT ε m β) : Result ε α → m (Result ε β)
  | .ok a    => f a
  | .error e => Pure.pure (.error e)
  | .fatal e => Pure.pure (.fatal e)

@[inline]
def bind {α β : Type u} (ma : ResultT ε m α) (f : α → ResultT ε m β) : ResultT ε m β :=
  .mk (ma >>= bindCont f)

end ResultT

end TParser
