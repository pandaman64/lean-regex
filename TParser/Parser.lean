import TParser.Box
import TParser.Success
import TParser.Result

set_option autoImplicit false

open String (Iterator)
open TParser (Success)
open TParser.Indexed

namespace TParser

/--
Lean 4 port of ["Total Parser Combinator"](https://github.com/gallais/agdarsec) from Guillaume Allais.

This version hard-codes the input type to `String.Iterator`.
-/
structure Parser (m : Type → Type) (α : Type) (n : Nat) where
  run {it : Iterator} (h : it.remainingBytes ≤ n) : m (Success α it.remainingBytes)

def SimpleParser (ε : Type) := Parser (Result ε)

namespace Parser

def parse {m α} [Monad m] (p : All (Parser m α)) (input : String) : m α := do
  let suc ← @p.run input.mkIterator (Nat.le_refl _)
  return suc.val

def parseCompleteOrElse {m α} [Monad m] (p : All (Parser m α)) (input : String) (remainingInput : m α) : m α := do
  let suc ← @p.run input.mkIterator (Nat.le_refl _)
  if suc.it.atEnd then
    return suc.val
  else
    remainingInput

def debug {m α} [Monad m] [ToString α] (name : String) : All (Imp (Parser m α) (Parser m α))
  | n, ⟨run⟩ => Parser.mk fun {it} h => dbgTrace s!"{name}: at {it.curr} ({n})" fun () => do
    let ⟨val, it', h'⟩ ← run h
    dbgTrace s!"{name} succeeded with {val}. Remaining {it'}" fun () => pure ⟨val, it', h'⟩

@[inline, specialize]
def map {m α β} [Functor m] (f : α → β) : All (Imp (Parser m α) (Parser m β))
  | _, ⟨run⟩ => Parser.mk fun h => Success.map f <$> run h

@[inline]
def mapConst {m α β} [Functor m] (a : α) : All (Imp (Parser m β) (Parser m α))
  | _, ⟨run⟩ => Parser.mk fun h => Success.mapConst a <$> run h

def failure {m α} [Alternative m] : All (Parser m α) :=
  Parser.mk fun _ => Alternative.failure

def orElse {m α} [∀ β, OrElse (m β)] : All (Imp (Parser m α) (Imp (Parser m α) (Parser m α)))
  | _, ⟨p⟩, ⟨q⟩ => Parser.mk fun h => p h <|> q h

def guardMOrElse {m α β} [Monad m] (f : α → Option β) (handler : All (App m (Success β))) : All (Imp (Parser m α) (Parser m β))
  | _, ⟨run⟩ => Parser.mk fun h => do
    match (← run h).guardM f with
    | .some s => pure s
    | .none => handler

def guardOrElse {m α} [Monad m] (f : α → Bool) (handler : All (App m (Success α))) : All (Imp (Parser m α) (Parser m α)) :=
  guardMOrElse (fun a => if f a then .some a else .none) handler

def guardM {m α β} [Monad m] [Alternative m] (f : α → Option β) : All (Imp (Parser m α) (Parser m β)) :=
  guardMOrElse f Alternative.failure

def guard {m α} [Monad m] [Alternative m] (f : α → Bool) : All (Imp (Parser m α) (Parser m α)) :=
  guardOrElse f Alternative.failure

def box {m α} : All (Imp (Parser m α) (Box (Parser m α))) :=
  Box.leClose (fun h ⟨run⟩ => Parser.mk fun h' => run (Nat.le_trans h' h))

def andBind {m α β} [Monad m] : All (Imp (Parser m α) (Imp (Imp (Const α) (Box (Parser m β))) (Parser m (α × β))))
  | _, p, q => Parser.mk fun h => do
    let ⟨a, it', h'⟩ ← p.run h
    let ⟨b, it'', h''⟩ ← ((q a).call (Nat.lt_of_lt_of_le h' h)).run (Nat.le_refl it'.remainingBytes)
    return ⟨(a, b), it'', Nat.lt_trans h'' h'⟩

def and {m α β} [Monad m] : All (Imp (Parser m α) (Imp (Box (Parser m β)) (Parser m (α × β))))
  | _, p, q => andBind p (fun _ => q)

def andBindR {m α β} [Monad m] : All (Imp (Parser m α) (Imp (Imp (Const α) (Box (Parser m β))) (Parser m β)))
  | _, p, q => (andBind p q).map (·.2)

def andBindM {m α β} [Monad m] : All (Imp (Parser m α) (Imp (Const (α → m β)) (Parser m β)))
  | _, p, f => Parser.mk fun h => do
    let ⟨a, it', h'⟩ ← p.run h
    let b ← f a
    return ⟨b, it', h'⟩

-- `andBindOpt p q` runs `p` and optionally followed by `q`.
def andBindOpt {m α β} [Monad m] [∀ γ, OrElse (m γ)] : All (Imp (Parser m α) (Imp (Imp (Const α) (Box (Parser m β))) (Parser m (α × Option β))))
  | _, p, q => Parser.mk fun h => do
    let ⟨a, it', h'⟩ ← p.run h
    let mb := ((q a).call (Nat.lt_of_lt_of_le h' h)).run (Nat.le_refl it'.remainingBytes)
    (fun ⟨b, it'', h''⟩ => ⟨(a, .some b), it'', Nat.lt_trans h'' h'⟩) <$> mb
      <|> pure ⟨(a, .none), it', h'⟩

def andOpt {m α β} [Monad m] [∀ γ, OrElse (m γ)] : All (Imp (Parser m α) (Imp (Box (Parser m β)) (Parser m (α × Option β))))
  | _, p, q => andBindOpt p (fun _ => q)

def some {m α} [Monad m] [∀ γ, OrElse (m γ)] (p : All (Parser m α)) : All (Parser m (List α))
  | _ => Box.fix fun rec => andOpt p rec |>.map (fun p => p.1 :: p.2.getD [])

def optAnd {m α β} [Monad m] [∀ γ, OrElse (m γ)] : All (Imp (Parser m α) (Imp (Parser m β) (Parser m (Option α × β))))
  | _, p, q => and (p.map .some) q.box |>.orElse (q.map (fun q => (Option.none, q)))

def LChain (m α) (n : Nat) := Success α n → Box (Parser m (α → α)) n → m (Success α n)

def schainlAux {m α} [Monad m] [∀ β, OrElse (m β)] : All (Imp (Box (LChain m α)) (LChain m α))
  | _, rec, ⟨a, it, h⟩, op =>
    let more := do
      let pop := op.call h
      let ⟨f, it', h'⟩ ← pop.run (Nat.le_refl it.remainingBytes)
      let result ← rec.call h ⟨f a, it', h'⟩ (op.castLT h)
      pure (result.castLT h)
    more <|> pure ⟨a, it, h⟩

-- Corresponds to `Success α → Parser m (α → α) → Success α`.
def schainl {m α} [Monad m] [∀ β, OrElse (m β)] : All (LChain m α)
  | _ => Box.fix fun rec => schainlAux rec

def iteratel {m α} [Monad m] [∀ β, OrElse (m β)] : All (Imp (Parser m α) (Imp (Box (Parser m (α → α))) (Parser m α)))
  | _, seed, op => Parser.mk fun h => do schainl (← seed.run h) (op.castLE h)

def foldl {m α β} [Monad m] [∀ γ, OrElse (m γ)] (init : β) (f : β → α → β) : All (Imp (Parser m α) (Parser m β))
  | _, elem => iteratel (elem.map fun a => f init a) (elem.map fun a accum => f accum a).box

def foldl1 {m α} [Monad m] [∀ β, OrElse (m β)] (f : α → α → α) : All (Imp (Parser m α) (Parser m α))
  | _, elem => (elem.andBindOpt (fun init => foldl init f elem |>.box)).map fun (elem₁, elems) => elems.getD elem₁

-- Corresponds to `Parser m α → Parser m (α → β → α) → Parser m β → Parser m α`.
def hchainl {m α β} [Monad m] [∀ γ, OrElse (m γ)] :
  All (Imp (Parser m α) (Imp (Box (Parser m (α → β → α)))
      (Imp (Box (Parser m β)) (Parser m α))))
  | _, seed, op, arg =>
    iteratel seed (Box.mk fun h =>
      let op' : Parser m (α → β → α) _ := op.call h
      let arg' : Box (Parser m β) _ := arg.duplicate.call h
      let opArg : Parser m ((α → β → α) × β) _ := op'.and arg'
      opArg.map fun (f, b) a => f a b
    )

def chainl1 {m α} [Monad m] [∀ β, OrElse (m β)] : All (Imp (Parser m α) (Imp (Box (Parser m (α → α → α))) (Parser m α)))
  | _, seed, op => hchainl seed op seed.box

def between' {m α β γ} [Monad m] : All (Imp (Parser m α) (Imp (Box (Parser m γ)) (Imp (Box (Parser m β)) (Parser m (α × β × γ)))))
  | _, l, r, m => l.and m |>.and r |>.map (fun ((a, b), c) => (a, b, c))

def between {m α β γ} [Monad m] : All (Imp (Parser m α) (Imp (Box (Parser m γ)) (Imp (Box (Parser m β)) (Parser m β))))
  | _, l, r, m => between' l r m |>.map (fun (_, b, _) => b)

end Parser

end TParser
