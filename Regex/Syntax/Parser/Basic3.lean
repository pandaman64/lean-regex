import Regex.Syntax.Ast

set_option autoImplicit false

open Regex.Syntax.Parser (Ast)
open Regex.Data (PerlClass PerlClassKind Class Classes Expr)
open String (Iterator)

namespace String.Iterator

@[simp]
theorem next'_remainingBytes_lt {it : Iterator} {h : it.hasNext} : (it.next' h).remainingBytes < it.remainingBytes := by
  simp [hasNext] at h
  simp [next', remainingBytes, String.next]
  have : (it.s.get it.i).utf8Size > 0 := Char.utf8Size_pos _
  omega

end String.Iterator

def LERel (it' it : Iterator) : Prop := it'.remainingBytes ≤ it.remainingBytes

def LTRel (it' it : Iterator) : Prop := it'.remainingBytes < it.remainingBytes

def Result.Rel (s : Bool) : Iterator → Iterator → Prop :=
  if s then LTRel else LERel

namespace Result.Rel

instance : Trans LERel LERel LERel where
  trans h h' := Nat.le_trans h h'

instance : Trans LERel LTRel LTRel where
  trans h h' := Nat.lt_of_le_of_lt h h'

instance : Trans LTRel LERel LTRel where
  trans h h' := Nat.lt_of_lt_of_le h h'

instance : Trans LTRel LTRel LTRel where
  trans h h' := Nat.lt_trans h h'

def weaken {s it' it} (h : Result.Rel s it' it) : Result.Rel false it' it :=
  match s with
  | true => Nat.le_of_lt h
  | false => h

def imp {s₁ s₂ : Bool} {it' it} (h : s₂ → s₁) (rel : Result.Rel s₁ it' it) : Result.Rel s₂ it' it :=
  match s₁, s₂ with
  | false, false => rel
  | false, true => by simp at h
  | true, false => rel.weaken
  | true, true => rel

def transOr {s₁ s₂ it it' it''} (h : Rel s₁ it it') (h' : Rel s₂ it' it'') : Result.Rel (s₁ || s₂) it it'' := by
  match s₁, s₂ with
  | false, false =>
    simp [Result.Rel] at *
    exact Trans.trans h h'
  | false, true =>
    simp [Result.Rel] at *
    exact Trans.trans h h'
  | true, false =>
    simp [Result.Rel] at *
    exact Trans.trans h h'
  | true, true =>
    simp [Result.Rel] at *
    exact Trans.trans h h'

def trans {s it it' it''} (h : Result.Rel s it it') (h' : Result.Rel s it' it'') : Result.Rel s it it'' :=
  (Bool.or_self s) ▸ transOr h h'

instance {s₁ s₂} : Trans (Result.Rel s₁) (Result.Rel s₂) (Result.Rel (s₁ || s₂)) where
  trans := transOr

instance {s} : Trans (Result.Rel s) (Result.Rel s) (Result.Rel s) where
  trans := trans

end Result.Rel

inductive Result (strict : Bool) (it : Iterator) (ε α : Type) where
  | ok : α → (it' : Iterator) → Result.Rel strict it' it → Result strict it ε α
  | error : ε → Result strict it ε α
  | fatal : ε → Result strict it ε α
deriving Repr

namespace Result

abbrev LE (it : Iterator) (ε α : Type) := Result false it ε α

abbrev LT (it : Iterator) (ε α : Type) := Result true it ε α

def transOr {s₁ s₂ it it' ε α} (h : Rel s₂ it' it) : Result s₁ it' ε α → Result (s₁ || s₂) it ε α
  | .ok a it'' h' => .ok a it'' (Result.Rel.transOr h' h)
  | .error e => .error e
  | .fatal e => .fatal e

def trans {s it it' ε α} (h : Rel s it it') : Result s it ε α → Result s it' ε α
  | .ok a it'' h' => .ok a it'' (Result.Rel.trans h' h)
  | .error e => .error e
  | .fatal e => .fatal e

def imp {s₁ s₂ : Bool} {it ε α} (h : s₂ → s₁) : Result s₁ it ε α → Result s₂ it ε α
  | .ok a it' h' => .ok a it' (h'.imp h)
  | .error e => .error e
  | .fatal e => .fatal e

def cast {s₁ s₂ it ε α} (h : s₁ = s₂) (res : Result s₁ it ε α) : Result s₂ it ε α :=
  res.imp (by simp [h])

def weaken {s it ε α} (res : Result s it ε α) : Result false it ε α :=
  res.imp (by simp)

def toExcept {s it ε α} (res : Result s it ε α) : Except ε α :=
  match res with
  | .ok a _ _ => .ok a
  | .error e => .error e
  | .fatal e => .error e

def opt {s it ε α} : Result s it ε α → Result false it ε (Option α)
  | .ok a it' h => .ok (.some a) it' h.weaken
  | .error _ => .ok .none it (Nat.le_refl _)
  | .fatal e => .fatal e

def complete {s it ε α} (expectedEof : ε) : Result s it ε α → Result s it ε α
  | .ok a it' h =>
    if it'.atEnd then
      .ok a it' h
    else
      .error expectedEof
  | .error e => .error e
  | .fatal e => .fatal e

def guard {s it ε α β} (f : α → Except ε β) : Result s it ε α → Result s it ε β
  | .ok a it' h =>
    match f a with
    | .ok b => .ok b it' h
    | .error e => .error e
  | .error e => .error e
  | .fatal e => .fatal e

def map' {s it ε α β} (f : α → (it' : Iterator) → Result.Rel s it' it → β) : Result s it ε α → Result s it ε β
  | .ok a it' h => .ok (f a it' h) it' h
  | .error e => .error e
  | .fatal e => .fatal e

def map {s it ε α β} (f : α → β) : Result s it ε α → Result s it ε β :=
  map' fun a _ _ => f a

def seq {s it ε α β} (mf : Result s it ε (α → β)) (mx : Unit → Result s it ε α) : Result s it ε β :=
  match mf with
  | .ok f _ _ =>
    match mx () with
    | .ok a it'' h' => .ok (f a) it'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

def seqLeft {s it ε α β} (mx : Result s it ε α) (my : Unit → Result s it ε β) : Result s it ε α :=
  match mx with
  | .ok a _ _ =>
    match my () with
    | .ok _ it'' h' => .ok a it'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

def seqRight {s it ε α β} (mx : Result s it ε α) (my : Unit → Result s it ε β) : Result s it ε β :=
  match mx with
  | .ok _ _ _ =>
    match my () with
    | .ok b it'' h' => .ok b it'' h'
    | .error e => .error e
    | .fatal e => .fatal e
  | .error e => .error e
  | .fatal e => .fatal e

def hOrElse {s₁ s₂ it ε α} (mx : Result s₁ it ε α) (my : Unit → Result s₂ it ε α) : Result (s₁ && s₂) it ε α :=
  match mx with
  | .ok a it' h => .ok a it' (h.imp (by simp_all))
  | .error _ => (my ()).imp (by simp)
  | .fatal e => .fatal e

def orElse {s it ε α} : Result s it ε α → (Unit → Result s it ε α) → Result s it ε α
  | .ok a it' h, _ => .ok a it' h
  | .error _, b => b ()
  | .fatal e, _ => .fatal e

def throw {s it ε α} (e : ε) : Result s it ε α := .error e

def tryCatch {s it ε α} (mx : Result s it ε α) (handle : ε → Result s it ε α) : Result s it ε α :=
  match mx with
  | .ok a it' h => .ok a it' h
  | .error e => handle e
  | .fatal e => .fatal e

def bind' {s₁ s₂ it ε α β} (mx : Result s₁ it ε α) (f : α → (it' : Iterator) → Result.Rel s₁ it' it → Result s₂ it' ε β) : Result (s₁ || s₂) it ε β :=
  match mx with
  | .ok a it' h => (f a it' h).transOr h |>.cast (Bool.or_comm _ _)
  | .error e => .error e
  | .fatal e => .fatal e

def bind {s it ε α β} (mx : Result s it ε α) (f : α → Result s it ε β) : Result s it ε β :=
  match mx with
  | .ok a _ _ => f a
  | .error e => .error e
  | .fatal e => .fatal e

def pure {it ε α} (a : α) : LE it ε α := .ok a it (Nat.le_refl _)

instance {s it ε} : Functor (Result s it ε) where
  map := map

instance {s it ε} : Seq (Result s it ε) where
  seq := seq

instance {s it ε} : SeqLeft (Result s it ε) where
seqLeft := seqLeft

instance {s it ε} : SeqRight (Result s it ε) where
  seqRight := seqRight

instance {s₁ s₂ it ε α} : HOrElse (Result s₁ it ε α) (Result s₂ it ε α) (Result (s₁ && s₂) it ε α) where
  hOrElse := hOrElse

instance {s it ε α} : OrElse (Result s it ε α) where
  orElse := orElse

instance {s it ε} : MonadExceptOf ε (Result s it ε) where
  throw := throw
  tryCatch := tryCatch

instance {s it ε} : Bind (Result s it ε) where
  bind := bind

instance {it ε} : Pure (LE it ε) where
  pure := pure

instance {it ε} : Monad (LE it ε) where
  bind := bind

end Result

abbrev Parser (s ε α) := ∀ (it : Iterator), Result s it ε α

namespace Parser

abbrev LE (ε α) := Parser false ε α

abbrev LT (ε α) := Parser true ε α

def imp {s₁ s₂ : Bool} {ε α} (h : s₂ → s₁) : Parser s₁ ε α → Parser s₂ ε α
  | p, it => (p it).imp h

def weaken {s ε α} : Parser s ε α → Parser false ε α
  | p, it => (p it).weaken

def cast {s₁ s₂ ε α} (h : s₁ = s₂) : Parser s₁ ε α → Parser s₂ ε α
  | p, it => (p it).cast h

def opt {s ε α} : Parser s ε α → Parser false ε (Option α)
  | p, it => (p it).opt

def guard {s ε α β} (f : α → Except ε β) : Parser s ε α → Parser s ε β
  | p, it => (p it).guard f

def complete {s ε α} (expectedEof : ε) : Parser s ε α → Parser s ε α
  | p, it => (p it).complete expectedEof

def debug {s ε α} [ToString α] (name : String) (p : Parser s ε α) : Parser s ε α
  | it => dbgTrace s!"Parsing {name} at {it}" fun () =>
    (p it).map (fun a => dbgTrace s!"parsed {a}" (fun () => a))

def map {s ε α β} (f : α → β) : Parser s ε α → Parser s ε β
  | p, it => (p it).map f

def mapConst {s ε α β} (a : α) : Parser s ε β → Parser s ε α
  | p, it => (p it).map (fun _ => a)

def seq {s ε α β} (p : Parser s ε (α → β)) (q : Unit → Parser s ε α) : Parser s ε β
  | it =>
    match p it with
    | .ok f it' h => (q () it').trans h |>.map f
    | .error e => .error e
    | .fatal e => .fatal e

def seqLeft {s ε α β} (p : Parser s ε α) (q : Unit → Parser s ε β) : Parser s ε α
  | it =>
    match p it with
    | .ok a it' h => (q () it').trans h |>.map (fun _ => a)
    | .error e => .error e
    | .fatal e => .fatal e

def seqRight {s ε α β} (p : Parser s ε α) (q : Unit → Parser s ε β) : Parser s ε β
  | it =>
    match p it with
    | .ok _ it' h => (q () it').trans h
    | .error e => .error e
    | .fatal e => .fatal e

def hOrElse {s₁ s₂ ε α} (p : Parser s₁ ε α) (q : Unit → Parser s₂ ε α) : Parser (s₁ && s₂) ε α
  | it =>
    match p it with
    | .ok a it' h => .ok a it' (h.imp (by simp_all))
    | .error _ => (q () it).imp (by simp)
    | .fatal e => .fatal e

def orElse {s ε α} (p : Parser s ε α) (q : Unit → Parser s ε α) : Parser s ε α
  | it =>
    match p it with
    | .ok a it' h => .ok a it' h
    | .error _ => q () it
    | .fatal e => .fatal e

def throw {s ε α} (e : ε) : Parser s ε α := fun _ => .error e

def tryCatch {s ε α} (p : Parser s ε α) (handle : ε → Parser s ε α) : Parser s ε α
  | it =>
    match p it with
    | .ok a it' h => .ok a it' h
    | .error e => handle e it
    | .fatal e => .fatal e

def bindOr {s₁ s₂ ε α β} (p : Parser s₁ ε α) (f : α → Parser s₂ ε β) : Parser (s₂ || s₁) ε β
  | it =>
    match p it with
    | .ok a it' h => (f a it').transOr h
    | .error e => .error e
    | .fatal e => .fatal e

def bind {s ε α β} (p : Parser s ε α) (f : α → Parser s ε β) : Parser s ε β
  | it =>
    match p it with
    | .ok a it' h => (f a it').trans h
    | .error e => .error e
    | .fatal e => .fatal e

def pure {ε α} (a : α) : Parser false ε α
  | it => .ok a it (Nat.le_refl _)

-- Lean can synthesize instances for `LT` only when declared explicitly.
instance {s ε} : Functor (Parser s ε) where
  map := map

instance {s ε} : Seq (Parser s ε) where
  seq := seq

instance {s ε} : SeqLeft (Parser s ε) where
  seqLeft := seqLeft

instance {s ε} : SeqRight (Parser s ε) where
  seqRight := seqRight

instance {s₁ s₂ ε α} : HOrElse (Parser s₁ ε α) (Parser s₂ ε α) (Parser (s₁ && s₂) ε α) where
  hOrElse := hOrElse

instance {s ε α} : OrElse (Parser s ε α) where
  orElse := orElse

instance {s ε} : MonadExceptOf ε (Parser s ε) where
  throw := throw
  tryCatch := tryCatch

instance {s ε} : Bind (Parser s ε) where
  bind := bind

instance {ε} : Pure (Parser false ε) where
  pure := pure

instance {ε} : Monad (Parser false ε) where
  bind := bind

end Parser

-- Use `@[macro_inline]` to avoid evaluating `unexpectedEof` eagerly.
@[macro_inline]
def anyCharOrElse {ε} (unexpectedEof : ε) : Parser.LT ε Char
  | it =>
    if hn : it.hasNext then
      .ok (it.curr' hn) (it.next' hn) Iterator.next'_remainingBytes_lt
    else
      .error unexpectedEof

@[macro_inline]
def test {ε} (c : Char) : Parser.LE ε Bool
  | it =>
    if hn : it.hasNext then
      .ok (it.curr' hn == c) (it.next' hn) (Nat.le_of_lt Iterator.next'_remainingBytes_lt)
    else
      pure false

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

def foldl1 {ε α} (f : α → α → α) (p : Parser.LT ε α) : Parser.LT ε α :=
  p.bindOr fun a => foldl a f p

def many1 {ε α} (p : Parser.LT ε α) : Parser.LT ε (Array α) :=
  p.bindOr fun a => foldl #[a] (fun acc a => acc.push a) p

def foldlNLE {ε α β} (init : β) (f : β → α → β) (p : Parser.LT ε α) (n : Nat) : Parser.LE ε β :=
  match n with
  | 0 => pure init
  | n' + 1 => fun it =>
    match p it with
    | .ok a it' h => foldlNLE (f init a) f p n' it' |>.transOr h |>.weaken
    | .error e => .error e
    | .fatal e => .fatal e

def foldlNLT {ε α β} (init : β) (f : β → α → β) (p : Parser.LT ε α) (n : Nat) [NeZero n] : Parser.LT ε β :=
  p.bindOr fun a => foldlNLE (f init a) f p (n - 1)

def betweenOr {s₁ s₂ s₃ ε α β γ} (l : Parser s₁ ε α) (r : Parser s₃ ε γ) (m : Parser s₂ ε β) : Parser (s₁ || s₂ || s₃) ε β :=
  (l.bindOr fun _ => m.bindOr fun x => r.mapConst x)
  |>.cast (by decide +revert)

inductive Error where
  | unexpectedEof
  | unexpectedChar (c : Char)
  | unexpectedEscapedChar (c : Char)
  | unexpectedPerlClass (cls : PerlClass)
  | unexpectedPerlClassInRange (cls : PerlClass)
  | invalidDigit (c : Char)
  | invalidHexDigit (c : Char)
  | invalidRange (c₁ : Char) (c₂ : Char)
  | invalidRepetition (min : Nat) (max : Nat)
  | expectedEof
deriving Repr

instance : ToString Error where
  toString := fun e =>
    match e with
    | .unexpectedEof => "unexpected EOF"
    | .unexpectedChar c => s!"unexpected character: {c}"
    | .unexpectedEscapedChar c => s!"unexpected escaped character: {c}"
    | .unexpectedPerlClass cls => s!"unexpected Perl class: {reprStr cls}"
    | .unexpectedPerlClassInRange cls => s!"unexpected Perl class in range: {reprStr cls}"
    | .invalidDigit c => s!"invalid digit: {c}"
    | .invalidHexDigit c => s!"invalid hex digit: {c}"
    | .invalidRange c₁ c₂ => s!"invalid range: {c₁}..{c₂}"
    | .invalidRepetition min max => s!"invalid repetition: {min}..{max}"
    | .expectedEof => "expected EOF"

def anyCharOrError : Parser.LT Error Char :=
  anyCharOrElse .unexpectedEof

def charOrError (c : Char) : Parser.LT Error Char :=
  charOrElse c .unexpectedEof .unexpectedChar

def charNotOrError (c : Char) : Parser.LT Error Char :=
  charNotOrElse c .unexpectedEof .unexpectedChar

def digit : Parser.LT Error Nat :=
  anyCharOrError
  |>.guard fun c =>
    if c.isDigit then .ok (c.toNat - '0'.toNat)
    else .error (.unexpectedChar c)

def number : Parser.LT Error Nat :=
  foldl1 (fun n d => 10 * n + d) digit

def hexDigit : Parser.LT Error Nat :=
  anyCharOrError |>.guard fun c =>
    if c.isDigit then .ok (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10)
    else .error (.unexpectedChar c)

def hexNumberN (n : Nat) [NeZero n] : Parser.LT Error Nat :=
  foldlNLT 0 (fun n d => 16 * n + d) hexDigit n

def escapedChar : Parser.LT Error (Char ⊕ PerlClass) :=
  charOrError '\\' *>
    (.inl <$> (simple <|> hex2 <|> hex4)) <|> (.inr <$> perlClass)
where
  simple : Parser.LT Error Char :=
    anyCharOrError
    |>.guard fun c =>
      match c with
      | 'n' => pure '\n'
      | 't' => pure '\t'
      | 'r' => pure '\r'
      | 'a' => pure '\x07'
      | 'f' => pure '\x0c'
      | 'v' => pure '\x0b'
      | '0' => pure '\x00'
      | '-' => pure '-'
      | '\\' => pure '\\'
      | _ => throw (.unexpectedEscapedChar c)
  hex2 : Parser.LT Error Char :=
    charOrError 'x' *> Char.ofNat <$> hexNumberN 2
  -- TODO: support "\u{XXXX}" and "\u{XXXXX}"
  hex4 : Parser.LT Error Char :=
    charOrError 'u' *> Char.ofNat <$> hexNumberN 4
  perlClass : Parser.LT Error PerlClass :=
    anyCharOrError
    |>.guard fun c =>
      match c with
      | 'd' => pure (PerlClass.mk false PerlClassKind.digit)
      | 'D' => pure (PerlClass.mk true PerlClassKind.digit)
      | 's' => pure (PerlClass.mk false PerlClassKind.space)
      | 'S' => pure (PerlClass.mk true PerlClassKind.space)
      | 'w' => pure (PerlClass.mk false PerlClassKind.word)
      | 'W' => pure (PerlClass.mk true PerlClassKind.word)
      | _ => throw (.unexpectedEscapedChar c)

def escapedCharToAst (c : Char ⊕ PerlClass) : Ast :=
  match c with
  | .inl c => .char c
  | .inr cls => .perl cls

def specialCharacters := "[](){}*+?|^$.\\"

def plainChar : Parser.LT Error Char :=
  anyCharOrError.guard fun c =>
    if specialCharacters.contains c then throw (.unexpectedChar c)
    else .ok c

def dot : Parser.LT Error Ast :=
  charOrError '.' |>.mapConst .dot

def charInClass : Parser.LT Error (Char ⊕ PerlClass) :=
  escapedChar <|> .inl <$> charNotOrError ']'

def singleClass : Parser.LT Error Class :=
  charInClass |>.bindOr fun f => do
    let isInterval ← test '-'
    if isInterval then
      match (← charInClass.opt) with
      | .some s =>
        let f ← ofExcept (expectsChar f)
        let s ← ofExcept (expectsChar s)
        if h : f ≤ s
          then pure (.range f s h)
          else throw (.invalidRange f s)
      | .none =>
        -- '-' just before ']' is treated as a normal character
        pure (.single '-')
    else
      match f with
      | .inl c => pure (.single c)
      | .inr cls => pure (.perl cls)
where
  expectsChar (c : Char ⊕ PerlClass) : Except Error Char :=
    match c with
    | .inl c => .ok c
    | .inr cls => .error (.unexpectedPerlClassInRange cls)

def classes : Parser.LT Error Ast :=
  betweenOr (charOrError '[') (charOrError ']') (do
    let negated ← test '^'
    let classes ← (many1 singleClass).weaken
    pure (.classes ⟨negated, classes⟩)
  )

def repetitionOp : Parser.LT Error (Nat × Option Nat) :=
  (charOrError '*' |>.mapConst (0, .none))
  <|> (charOrError '+' |>.mapConst (1, .none))
  <|> (charOrError '?' |>.mapConst (0, .some 1))
  <|> (betweenOr (charOrError '{') (charOrError '}') do
    let min ← number.weaken
    let comma ← test ','
    if comma then
      match (← number.opt) with
      | .some max =>
        if min ≤ max then
          pure (min, .some max) -- {N,M} represents N to M repetitions
        else
          throw (.invalidRepetition min max) -- {N,M} where N > M is invalid
      | .none => pure (min, .none) -- {N,} represents N or more repetitions
    else
      pure (min, .some min) -- {N} represents N repetitions
  )

def repeatConcat (ast : Ast) (n : Nat) : Ast :=
  go ast (n - 1)
where
  go (ast : Ast) : Nat → Ast
    | 0 => ast
    | n + 1 => .concat (go ast n) ast

def applyRepetition (min : Nat) (max : Option Nat) (ast : Ast) : Ast :=
  match min, max with
  -- special case for well-known repetitions
  | 0, .some 1 => .alternate ast .empty
  | 0, .none => .star ast
  | 1, .none => .concat ast (.star ast)
  -- r{min,}. min > 0 as `0, .none` is already covered.
  | min, .none => .concat (repeatConcat ast min) (.star ast)
  -- r{0,max}
  | 0, .some max =>
    if max == 0 then
      Ast.empty
    else
      repeatConcat (Ast.alternate ast Ast.empty) max
  | min, .some max =>
    if min == max then
      repeatConcat ast min
    else
      Ast.concat (repeatConcat ast min) (repeatConcat (Ast.alternate ast Ast.empty) (max - min))

mutual

def group (it : Iterator) : Result.LT it Error Ast :=
  charOrError '(' it
  |>.bind' fun _ it' _ =>
    regex it'
    |>.bind' fun ast it'' _ => Functor.mapConst ast (charOrError ')' it'')
termination_by (it.remainingBytes, 0)

def primary (it : Iterator) : Result.LT it Error Ast :=
  group it <|> classes it <|> dot it <|> escapedCharToAst <$> escapedChar it <|> .char <$> plainChar it
termination_by (it.remainingBytes, 10)

def repetition1 (ast : Ast) (it : Iterator) : Result.LE it Error Ast :=
  (repetitionOp it |>.bind' fun (min, max) it' _ => repetition1 (applyRepetition min max ast) it').weaken
  <|> pure ast
termination_by (it.remainingBytes, 20)

def repetition (it : Iterator) : Result.LT it Error Ast :=
  primary it |>.bind' fun ast it' _ => repetition1 ast it'
termination_by (it.remainingBytes, 21)

def concat1 (ast : Ast) (it : Iterator) : Result.LE it Error Ast :=
  (repetition it |>.bind' fun ast' it' _ => concat1 (.concat ast ast') it').weaken
  <|> pure ast
termination_by (it.remainingBytes, 30)

def concat (it : Iterator) : Result.LE it Error Ast :=
  (repetition it |>.bind' fun ast it' _ => concat1 ast it').weaken
  <|> pure .epsilon
termination_by (it.remainingBytes, 31)

def alternate1 (ast : Ast) (it : Iterator) : Result.LE it Error Ast :=
  (charOrError '|' it |>.bind' fun _ it' h =>
    concat it' |>.bind' fun ast' it'' h' =>
      have : LTRel it'' it := Trans.trans h' h
      alternate1 (.alternate ast ast') it''
  ).weaken
  <|> pure ast
termination_by (it.remainingBytes, 40)

def alternate (it : Iterator) : Result.LE it Error Ast :=
  concat it |>.bind' fun ast it' _ => alternate1 ast it'
termination_by (it.remainingBytes, 41)
decreasing_by
  . simp [Prod.lex_def]
  . simp [Prod.lex_def]
    exact Nat.lt_or_eq_of_le (by assumption)

def regex (it : Iterator) : Result.LE it Error Ast :=
  alternate it |>.weaken
termination_by (it.remainingBytes, 100)

end

def parse (input : String) : Except Error Ast :=
  regex input.mkIterator |>.complete .expectedEof |>.toExcept

def parse! (input : String) : Ast :=
  match parse input with
  | .ok r => r
  | .error e => panic! s!"Failed to parse a regex: {e}"
