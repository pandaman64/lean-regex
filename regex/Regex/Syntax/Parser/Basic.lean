import Regex.Syntax.Ast
import Regex.Syntax.Parser.Combinators
import Regex.Syntax.Parser.Error

set_option autoImplicit false

open Regex.Syntax.Parser (Ast)
open Regex.Syntax.Parser.Combinators
open Regex.Data (Anchor PerlClass PerlClassKind Class Classes Expr)
open String (Pos)

namespace Regex.Syntax.Parser

variable {s : String}

def anyCharOrError : Parser.LT s Error Char :=
  anyCharOrElse .unexpectedEof

def charOrError (c : Char) : Parser.LT s Error Char :=
  charOrElse c .unexpectedEof .unexpectedChar

def charOrErrorCommit (c : Char) : Parser.LT s Error Char :=
  charOrElse c .unexpectedEndOfInput .unexpectedChar

def digit : Parser.LT s Error Nat :=
  anyCharOrError
  |>.guard fun c =>
    if c.isDigit then .ok (c.toNat - '0'.toNat)
    else .error (.unexpectedChar c)

def number : Parser.LT s Error Nat :=
  foldl1 (fun n d => 10 * n + d) digit

def hexDigit : Parser.LT s Error Nat
  | pos =>
    match anyCharOrError pos with
    | .ok c pos' h =>
      if c = '}' then .error (.unexpectedChar c)
      else if c.isDigit then .ok (c.toNat - '0'.toNat) pos' h
      else if 'a' ≤ c && c ≤ 'f' then .ok (c.toNat - 'a'.toNat + 10) pos' h
      else if 'A' ≤ c && c ≤ 'F' then .ok (c.toNat - 'A'.toNat + 10) pos' h
      else .fatal (.invalidHexChar c)
    | .error e => .error e
    | .fatal e => .fatal e

def hexNumberN (n : Nat) [NeZero n] : Parser.LT s Error Nat :=
  foldlPos 0 (fun n d => 16 * n + d) hexDigit n

def specialCharacters := "[](){*+?|^$.\\"

def escapedChar : Parser.LT s Error (Char ⊕ PerlClass) :=
  charOrError '\\' *>
    ((Sum.inl <$> (simple <|> hexEscape)) <|> (Sum.inr <$> perlClass)).commit
where
  simple : Parser.LT s Error Char :=
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
      | '}' => pure '}'
      | c =>
        if specialCharacters.contains c then
          pure c
        else
          throw (.unexpectedEscapedChar c)
  hexEscape : Parser.LT s Error Char :=
    (charOrError 'x' *> (Char.ofNat <$> hexNumberN 2).commit)
    <|> (charOrError 'u' *> unicodeEscape.commit)
  unicodeEscape : Parser.LT s Error Char :=
    hexNumberVariable.guard fun n =>
      if n > 0x10FFFF then
        .error (.invalidCodePoint n)
      else if n >= 0xD800 && n <= 0xDFFF then
        .error (.invalidCodePoint n)
      else
        .ok (Char.ofNat n)
  hexNumberVariable : Parser.LT s Error Nat :=
    betweenOr (charOrError '{') (charOrErrorCommit '}').commit (.commit do
    let digits ← (many1 hexDigit).weaken
      if digits.size > 6 then
        throw (.tooManyHexDigits digits.size)
      else
        pure (digits.foldl (fun n d => 16 * n + d) 0)
    )
    <|> hexNumberN 4
  perlClass : Parser.LT s Error PerlClass :=
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

def plainChar : Parser.LT s Error Char :=
  anyCharOrError.guard fun c =>
    if specialCharacters.contains c then throw (.unexpectedChar c)
    else .ok c

def anchor : Parser.LT s Error Ast :=
  (charOrError '^' |>.mapConst (.anchor .start))
  <|> (charOrError '$' |>.mapConst (.anchor .eos))
  <|> (charOrError '\\' *> charOrError 'b' |>.mapConst (.anchor .wordBoundary))
  <|> (charOrError '\\' *> charOrError 'B' |>.mapConst (.anchor .nonWordBoundary))

def dot : Parser.LT s Error Ast :=
  charOrError '.' |>.mapConst .dot

def charInClass : Parser.LT s Error (Char ⊕ PerlClass) :=
  escapedChar <|> (anyCharOrError.guard fun c =>
    if c = ']' ∨ c = '\\' then throw (.unexpectedChar c)
    else .ok (.inl c)
  )

def range : Parser.LT s Error Class :=
  ((Prod.mk <$> charInClass) <*> (charOrError '-' *> charInClass))
  |>.guard fun (f, s) => do
    let f ← expectsChar f
    let s ← expectsChar s
    if f ≤ s then
      pure (.range f s)
    else
      throw (.invalidRange f s)
where
  expectsChar (c : Char ⊕ PerlClass) : Except Error Char :=
    match c with
    | .inl c => .ok c
    | .inr cls => .error (.unexpectedPerlClassInRange cls)

def singleClass : Parser.LT s Error Class :=
  range <|> (charToClass <$> charInClass)
where
  charToClass (c : Char ⊕ PerlClass) : Class :=
    match c with
    | .inl c => .single c
    | .inr cls => .perl cls

def classes : Parser.LT s Error Ast :=
  betweenOr (charOrError '[') (charOrError ']').commit (.commit do
    let negated ← test '^'
    let classes ← (many1 singleClass).weaken
    pure (Ast.classes ⟨negated, classes⟩)
  )

def repetitionInner : Parser.LT s Error (Nat × Option Nat) :=
  (charOrError '*' |>.mapConst (0, .none))
  <|> (charOrError '+' |>.mapConst (1, .none))
  <|> (charOrError '?' |>.mapConst (0, .some 1))
  <|> (betweenOr (charOrError '{') (charOrError '}').commit (.commit do
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
  ))

def repetitionOp : Parser.LT s Error (Nat × Option Nat × Bool) :=
  repetitionInner.bindOr fun (min, max) => do
    let nonGreedy ← test '?'
    pure (min, max, !nonGreedy)

def nonCapturing : Parser.LT s Error Unit :=
  charOrError '?' *> charOrError ':' |>.mapConst ()

/-
The following definitions describe the recursive structure of the regex parser. We duplicate the
loops in the grammar in several definitions like `repetition1` and `concat1` since our combinators
only work for a fully-defined parser (which can accept any input with arbitrary length), but the
mutually recursive functions can only work for an input that is strictly decreasing.

Total parser combinators a la [agdarsec](https://github.com/gallais/agdarsec) can provide parser
combinators that can be used in mutual recursion, but it requires a more elaborate infrastructure
like types indexed by a `Nat` to work. I found it more convenient to just duplicate the loops.
-/
mutual

def group (pos : Pos s) : Result.LT pos Error Ast :=
  (charOrError '(' pos)
  |>.bind' fun _ pos' h =>
    (nonCapturing.opt pos'
    |>.bind' fun nonCapturing pos'' h' =>
      have : Rel.LT pos'' pos := Trans.trans h' h
      regex pos''
      |>.bind' fun ast pos''' _ =>
        let ast := if nonCapturing.isSome then ast else .group ast
        Functor.mapConst ast (charOrError ')' pos''')).commit
termination_by (pos, 0)

def primary (pos : Pos s) : Result.LT pos Error Ast :=
  group pos
  <|> classes pos
  <|> dot pos
  <|> (anchor pos)
  <|> (escapedCharToAst <$> escapedChar pos)
  <|> (.char <$> plainChar pos)
termination_by (pos, 10)

def repetition1 (ast : Ast) (pos : Pos s) : Result.LE pos Error Ast :=
  (repetitionOp pos |>.bind' fun (min, max, greedy) pos' _ => repetition1 (.repeat min max greedy ast) pos').weaken
  <|> pure ast
termination_by (pos, 20)

def repetition (pos : Pos s) : Result.LT pos Error Ast :=
  primary pos |>.bind' fun ast pos' _ => repetition1 ast pos'
termination_by (pos, 21)

def concat1 (ast : Ast) (pos : Pos s) : Result.LE pos Error Ast :=
  (repetition pos |>.bind' fun ast' pos' _ => concat1 (.concat ast ast') pos').weaken
  <|> pure ast
termination_by (pos, 30)

def concat (pos : Pos s) : Result.LE pos Error Ast :=
  (repetition pos |>.bind' fun ast pos' _ => concat1 ast pos').weaken
  <|> pure .epsilon
termination_by (pos, 31)

def alternate1 (ast : Ast) (pos : Pos s) : Result.LE pos Error Ast :=
  (charOrError '|' pos |>.bind' fun _ pos' h =>
    concat pos' |>.bind' fun ast' pos'' h' =>
      have : Rel.LT pos'' pos := Trans.trans h' h
      alternate1 (.alternate ast ast') pos''
  ).weaken
  <|> pure ast
termination_by (pos, 40)

def alternate (pos : Pos s) : Result.LE pos Error Ast :=
  concat pos |>.bind' fun ast pos' _ => alternate1 ast pos'
termination_by (pos, 41)
decreasing_by
  . simp [Prod.lex_def]
  . rename_i h
    simp [Prod.lex_def]
    cases Nat.lt_or_eq_of_le h with
    | inl h => exact .inl h
    | inr h =>
      apply Or.inr
      ext
      exact h.symm

def regex (pos : Pos s) : Result.LE pos Error Ast :=
  alternate pos |>.weaken
termination_by (pos, 100)

end

def parseAst (input : String) : Except Error Ast :=
  regex input.startPos
  |>.complete .expectedEof
  |>.toExcept

def parse (input : String) : Except Error Expr :=
  parseAst input
  |>.map fun ast => Ast.toRegex (.group ast)

def parse! (input : String) : Expr :=
  match parse input with
  | .ok r => r
  | .error e => panic! s!"Failed to parse a regex: {e}"

end Regex.Syntax.Parser
