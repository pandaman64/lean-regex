import Regex.Syntax.Parser.Combinators.Parser
import Regex.Data.String

set_option autoImplicit false

open String (Iterator)

namespace Regex.Syntax.Parser.Combinators

@[macro_inline]
def anyCharOrElse {ε} (unexpectedEof : ε) : Parser.LT ε Char
  | it =>
    if hn : it.hasNext then
      .ok (it.curr' hn) (it.next' hn) Iterator.next'_remainingBytes_lt
    else
      .error unexpectedEof

@[macro_inline]
def testP {ε} (f : Char → Bool) : Parser.LE ε Bool
  | it =>
    if hn : it.hasNext then
      .ok (f (it.curr' hn)) (it.next' hn) (Nat.le_of_lt Iterator.next'_remainingBytes_lt)
    else
      pure false

@[macro_inline]
def test {ε} (c : Char) : Parser.LE ε Bool :=
  testP (· = c)

@[macro_inline]
def charOrElse {ε} (c : Char) (unexpectedEof : ε) (unexpectedChar : Char → ε) : Parser.LT ε Char
  | it =>
    anyCharOrElse unexpectedEof it |>.guard fun c' =>
      if c = c' then .ok c else .error (unexpectedChar c)

@[macro_inline]
def charNotOrElse {ε} (c : Char) (unexpectedEof : ε) (unexpectedChar : Char → ε) : Parser.LT ε Char
  | it =>
    anyCharOrElse unexpectedEof it |>.guard fun c' =>
      if c != c' then .ok c' else .error (unexpectedChar c)

def foldl {ε α β} (init : β) (f : β → α → β) (p : Parser.LT ε α) : Parser.LE ε β :=
  fun it =>
    match p it with
    | .ok a it' h => ((foldl (f init a) f p it').transOr h).weaken
    | .error _ => pure init
    | .fatal e => .fatal e

@[inline]
def foldl1 {ε α} (f : α → α → α) (p : Parser.LT ε α) : Parser.LT ε α :=
  p.bindOr fun a => foldl a f p

@[inline]
def many1 {ε α} (p : Parser.LT ε α) : Parser.LT ε (Array α) :=
  p.bindOr fun a => foldl #[a] (fun acc a => acc.push a) p

@[inline]
def betweenOr {s₁ s₂ s₃ ε α β γ} (l : Parser s₁ ε α) (r : Parser s₃ ε γ) (m : Parser s₂ ε β) : Parser (s₁ || s₂ || s₃) ε β :=
  (l.bindOr fun _ => m.bindOr fun x => r.mapConst x).cast (by decide +revert)

def foldlNAux {s ε α β} (init : β) (f : β → α → β) (p : Parser s ε α) (n : Nat) (it : Iterator) : Result (n ≠ 0 && s) it ε β :=
  match n with
  | 0 => (Result.pure init).imp (by simp)
  | n' + 1 =>
    match p it with
    | .ok a it' h => foldlNAux (f init a) f p n' it' |>.transOr h |>.imp (by simp_all)
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def foldlN {s ε α β} (init : β) (f : β → α → β) (p : Parser s ε α) (n : Nat) : Parser (n ≠ 0 && s) ε β
  | it => foldlNAux init f p n it

@[inline]
def foldlPos {ε α β} (init : β) (f : β → α → β) (p : Parser.LT ε α) (n : Nat) [NeZero n] : Parser.LT ε β :=
  foldlN init f p n |>.cast (by simp [NeZero.ne])

end Regex.Syntax.Parser.Combinators
