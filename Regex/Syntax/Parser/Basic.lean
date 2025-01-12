import Regex.Syntax.Ast
import Regex.Syntax.Parser.Combinators
import Regex.Syntax.Parser.Error

set_option autoImplicit false

open Regex.Syntax.Parser (Ast)
open Regex.Syntax.Parser.Combinators
open Regex.Data (PerlClass PerlClassKind Class Classes Expr)
open String (Iterator)

namespace Regex.Syntax.Parser

def anyCharOrError : Parser.LT Error Char :=
  anyCharOrElse .unexpectedEof

def charOrError (c : Char) : Parser.LT Error Char :=
  charOrElse c .unexpectedEof .unexpectedChar

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
  foldlPos 0 (fun n d => 16 * n + d) hexDigit n

def escapedChar : Parser.LT Error (Char ⊕ PerlClass) :=
  charOrError '\\' *>
    ((.inl <$> (simple <|> hex2 <|> hex4)) <|> (.inr <$> perlClass))
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
    charOrError 'x' *> (Char.ofNat <$> hexNumberN 2)
  -- TODO: support "\u{XXXX}" and "\u{XXXXX}"
  hex4 : Parser.LT Error Char :=
    charOrError 'u' *> (Char.ofNat <$> hexNumberN 4)
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
  escapedChar <|> (anyCharOrError.guard fun c =>
    if c = ']' ∨ c = '\\' then throw (.unexpectedChar c)
    else .ok (.inl c)
  )

def range : Parser.LT Error Class :=
  ((Prod.mk <$> charInClass) <*> (charOrError '-' *> charInClass))
  |>.guard fun (f, s) => do
    let f ← expectsChar f
    let s ← expectsChar s
    if h : f ≤ s then
      pure (.range f s h)
    else
      throw (.invalidRange f s)
where
  expectsChar (c : Char ⊕ PerlClass) : Except Error Char :=
    match c with
    | .inl c => .ok c
    | .inr cls => .error (.unexpectedPerlClassInRange cls)

def singleClass : Parser.LT Error Class :=
  range <|> (charToClass <$> charInClass)
where
  charToClass (c : Char ⊕ PerlClass) : Class :=
    match c with
    | .inl c => .single c
    | .inr cls => .perl cls

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
  go (accum : Ast) : Nat → Ast
    | 0 => accum
    | n + 1 => go (.concat accum ast) n

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

def nonCapturing : Parser.LT Error Unit :=
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

def group (it : Iterator) : Result.LT it Error Ast :=
  (charOrError '(' it)
  |>.bind' fun _ it' h =>
    nonCapturing.opt it'
    |>.bind' fun nonCapturing it'' h' =>
      have : Rel.LT it'' it := Trans.trans h' h
      regex it''
      |>.bind' fun ast it''' _ =>
        let ast := if nonCapturing.isSome then ast else .group ast
        Functor.mapConst ast (charOrError ')' it''')
termination_by (it.remainingBytes, 0)

def primary (it : Iterator) : Result.LT it Error Ast :=
  group it <|> classes it <|> dot it <|> (escapedCharToAst <$> escapedChar it) <|> (.char <$> plainChar it)
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
      have : Rel.LT it'' it := Trans.trans h' h
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

def parseAst (input : String) : Except Error Ast :=
  regex input.mkIterator
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
