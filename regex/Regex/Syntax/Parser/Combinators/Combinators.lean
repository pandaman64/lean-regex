import Regex.Syntax.Parser.Combinators.Parser
import Regex.Data.String

set_option autoImplicit false

open String (Pos)

namespace Regex.Syntax.Parser.Combinators

@[macro_inline]
def anyCharOrElse {s ε} (unexpectedEof : ε) : Parser.LT s ε Char
  | pos =>
    if hn : pos ≠ s.endPos then
      .ok (pos.get hn) (pos.next hn) pos.lt_next
    else
      .error unexpectedEof

@[macro_inline]
def testP {s ε} (f : Char → Bool) : Parser.LE s ε Bool
  | pos =>
    if hn : pos ≠ s.endPos then
      let b := f (pos.get hn)
      if b then
        .ok b (pos.next hn) (Nat.le_of_lt pos.lt_next)
      else
        pure false
    else
      pure false

@[macro_inline]
def test {s ε} (c : Char) : Parser.LE s ε Bool :=
  testP (· = c)

@[macro_inline]
def charOrElse {s ε} (c : Char) (unexpectedEof : ε) (unexpectedChar : Char → ε) : Parser.LT s ε Char
  | pos =>
    anyCharOrElse unexpectedEof pos |>.guard fun c' =>
      if c = c' then .ok c else .error (unexpectedChar c')

def foldlAux {s ε α β} (init : β) (f : β → α → β) (p : Parser.LT s ε α) (pos : Pos s) : Result.LE pos ε β :=
  match p pos with
  | .ok a pos' h => ((foldlAux (f init a) f p pos').transOr h).weaken
  | .error _ => pure init
  | .fatal e => .fatal e
termination_by pos

def foldl {s ε α β} (init : β) (f : β → α → β) (p : Parser.LT s ε α) : Parser.LE s ε β :=
  foldlAux init f p

@[inline]
def foldl1 {s ε α} (f : α → α → α) (p : Parser.LT s ε α) : Parser.LT s ε α :=
  p.bindOr fun a => foldl a f p

@[inline]
def many1 {s ε α} (p : Parser.LT s ε α) : Parser.LT s ε (Array α) :=
  p.bindOr fun a => foldl #[a] (fun acc a => acc.push a) p

@[inline]
def betweenOr {s strict₁ strict₂ strict₃ ε α β γ} (l : Parser s strict₁ ε α) (r : Parser s strict₃ ε γ) (m : Parser s strict₂ ε β) : Parser s (strict₁ || strict₂ || strict₃) ε β :=
  (l.bindOr fun _ => m.bindOr fun x => r.mapConst x).cast (by grind)

def foldlNAux {s strict ε α β} (init : β) (f : β → α → β) (p : Parser s strict ε α) (n : Nat) (pos : Pos s) : Result (n ≠ 0 && strict) pos ε β :=
  match n with
  | 0 => (Result.pure init).imp (by simp)
  | n' + 1 =>
    match p pos with
    | .ok a pos' h => foldlNAux (f init a) f p n' pos' |>.transOr h |>.imp (by simp_all)
    | .error e => .error e
    | .fatal e => .fatal e

@[inline]
def foldlN {s strict ε α β} (init : β) (f : β → α → β) (p : Parser s strict ε α) (n : Nat) : Parser s (n ≠ 0 && strict) ε β
  | pos => foldlNAux init f p n pos

@[inline]
def foldlPos {s ε α β} (init : β) (f : β → α → β) (p : Parser.LT s ε α) (n : Nat) [NeZero n] : Parser.LT s ε β :=
  foldlN init f p n |>.cast (by simp [NeZero.ne])

end Regex.Syntax.Parser.Combinators
