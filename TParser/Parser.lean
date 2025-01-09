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

@[inline, specialize]
def anyChar {m} [Alternative m] : All (Parser m Char) :=
  Parser.mk fun {it} h =>
    if hn : it.hasNext then
      pure ⟨it.curr' hn, it.next' hn, by simp [Iterator.next_remainingBytes_lt, hn]⟩
    else
      failure

@[inline, specialize]
def map {m α β} [Functor m] (f : α → β) : All (Imp (Parser m α) (Parser m β))
  | _, ⟨run⟩ => Parser.mk fun h => Success.map f <$> run h

def guardM {m α β} [Functor m] (f : α → Option β) : All (Imp (Parser m α) (Parser m (Option β)))
  | _, ⟨run⟩ => Parser.mk fun h => Success.map f <$> run h

def failure {m α} [Alternative m] : All (Parser m α) :=
  Parser.mk fun _ => Alternative.failure

def orElse {m α} [Alternative m] : All (Imp (Parser m α) (Imp (Parser m α) (Parser m α)))
  | _, ⟨p⟩, ⟨q⟩ => Parser.mk fun h => p h <|> q h

def box {m α} : All (Imp (Parser m α) (Box (Parser m α))) :=
  Box.leClose (fun h ⟨run⟩ => Parser.mk fun h' => run (Nat.le_trans h' h))

def andBind {m α β} [Monad m] : All (Imp (Parser m α) (Imp (Imp (Const α) (Box (Parser m β))) (Parser m (α × β))))
  | _, p, q => Parser.mk fun h => do
    let ⟨a, it', h'⟩ ← p.run h
    let ⟨b, it'', h''⟩ ← ((q a).call (Nat.lt_of_lt_of_le h' h)).run (Nat.le_refl it'.remainingBytes)
    return ⟨(a, b), it'', Nat.lt_trans h'' h'⟩

def and {m α β} [Monad m] : All (Imp (Parser m α) (Imp (Box (Parser m β)) (Parser m (α × β))))
  | _, p, q => andBind p (fun _ => q)

-- `andBindOpt p q` runs `p` and optionally followed by `q`.
def andBindOpt {m α β} [Monad m] [Alternative m] : All (Imp (Parser m α) (Imp (Imp (Const α) (Box (Parser m β))) (Parser m (α × Option β))))
  | _, p, q => Parser.mk fun h => do
    let ⟨a, it', h'⟩ ← p.run h
    let mb := ((q a).call (Nat.lt_of_lt_of_le h' h)).run (Nat.le_refl it'.remainingBytes)
    (fun ⟨b, it'', h''⟩ => ⟨(a, .some b), it'', Nat.lt_trans h'' h'⟩) <$> mb
      <|> pure ⟨(a, .none), it', h'⟩

def andOpt {m α β} [Monad m] [Alternative m] : All (Imp (Parser m α) (Imp (Box (Parser m β)) (Parser m (α × Option β))))
  | _, p, q => andBindOpt p (fun _ => q)

def some {m α} [Monad m] [Alternative m] (p : All (Parser m α)) : All (Parser m (List α))
  | _ => Box.fix fun rec => andOpt p rec |>.map (fun p => p.1 :: p.2.getD [])

def optAnd {m α β} [Monad m] [Alternative m] : All (Imp (Parser m α) (Imp (Parser m β) (Parser m (Option α × β))))
  | _, p, q => and (p.map .some) q.box |>.orElse (q.map (fun q => (Option.none, q)))

def LChain (m α) (n : Nat) := Success α n → Box (Parser m (α → α)) n → m (Success α n)

def schainlAux {m α} [Monad m] [Alternative m] : All (Imp (Box (LChain m α)) (LChain m α))
  | _, rec, ⟨a, it, h⟩, op =>
    let more := do
      let pop := op.call h
      let ⟨f, it', h'⟩ ← pop.run (Nat.le_refl it.remainingBytes)
      let result ← rec.call h ⟨f a, it', h'⟩ (op.castLT h)
      pure (result.castLT h)
    more <|> pure ⟨a, it, h⟩

-- Corresponds to `Success α → Parser m (α → α) → Success α`.
def schainl {m α} [Monad m] [Alternative m] : All (LChain m α)
  | _ => Box.fix fun rec => schainlAux rec

def iteratel {m α} [im : Monad m] [ia : Alternative m] : All (Imp (Parser m α) (Imp (Box (Parser m (α → α))) (Parser m α)))
  | _, seed, op => Parser.mk fun h => do schainl (← seed.run h) (op.castLE h)

-- Corresponds to `Parser m α → Parser m (α → β → α) → Parser m β → Parser m α`.
def hchainl {m α β} [Monad m] [Alternative m] :
  All (Imp (Parser m α) (Imp (Box (Parser m (α → β → α)))
      (Imp (Box (Parser m β)) (Parser m α))))
  | _, seed, op, arg =>
    iteratel seed (Box.mk fun h =>
      let op' : Parser m (α → β → α) _ := op.call h
      let arg' : Box (Parser m β) _ := arg.duplicate.call h
      let opArg : Parser m ((α → β → α) × β) _ := op'.and arg'
      opArg.map fun (f, b) a => f a b
    )

def chainl1 {m α} [Monad m] [Alternative m] : All (Imp (Parser m α) (Imp (Box (Parser m (α → α → α))) (Parser m α)))
  | _, seed, op => hchainl seed op seed.box

end Parser

end TParser
