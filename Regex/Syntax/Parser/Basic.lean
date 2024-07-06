import Regex.Syntax.Ast
import Regex.Syntax.Parser.ParserAux

open Regex.Data (PerlClass PerlClassKind Class Expr)
open Parser
open Parser.Char

namespace Regex.Syntax.Parser

def specialCharacters := "[](){}*+?|^$.\\"

abbrev Parser := SimpleParser Substring Char

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def digitToInt (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat
  else if 'a' ≤ c && c ≤ 'f' then c.toNat - 'a'.toNat + 10
  else if 'A' ≤ c && c ≤ 'F' then c.toNat - 'A'.toNat + 10
  else panic! "digitToInt: not a digit"

-- NOTE: I don't have any idea if the precedence or any other stuff are correct here
mutual

partial def escaped (withPerlClasses: Bool) : Parser (if withPerlClasses then Ast else Char) :=
  withErrorMessage "expected an escaped character" do
    let _ ← token '\\'
    let c ← anyToken
    let escape (c: Char) : Parser Char :=
      match c with
      | 'n' => pure '\n'
      | 't' => pure '\t'
      | 'r' => pure '\r'
      | 'a' => pure '\x07'
      | 'f' => pure '\x0c'
      | 'v' => pure '\x0b'
      | '0' => pure '\x00'
      | 'x' => do
        let d₁ ← tokenFilter isHexDigit
        let d₂ ← tokenFilter isHexDigit
        let n ← pure (16 * digitToInt d₁ + digitToInt d₂)
        pure (Char.ofNat n)
      | 'u' => do
        let bracket ← option? $ tokenFilter (· == '{')
        let d₁ ← tokenFilter isHexDigit
        let d₂ ← tokenFilter isHexDigit
        let d₃ ← tokenFilter isHexDigit
        let d₄ ← tokenFilter isHexDigit
        if bracket.isSome then
          let _ ← token '}'
        let n ← pure (4096 * digitToInt d₁ + 256 * digitToInt d₂ + 16 * digitToInt d₃ + digitToInt d₄)
        pure (Char.ofNat n)
      | _   => pure c

    let perlClasses (c: Char) : Parser Ast :=
      match c with
      | 'd' => pure (Ast.perl (PerlClass.mk false PerlClassKind.digit))
      | 'D' => pure (Ast.perl (PerlClass.mk true PerlClassKind.digit))
      | 's' => pure (Ast.perl (PerlClass.mk false PerlClassKind.space))
      | 'S' => pure (Ast.perl (PerlClass.mk true PerlClassKind.space))
      | 'w' => pure (Ast.perl (PerlClass.mk false PerlClassKind.word))
      | 'W' => pure (Ast.perl (PerlClass.mk true PerlClassKind.word))
      |  _  => throwUnexpected

    match withPerlClasses with
    | true  => perlClasses c <|> (Ast.char <$> escape c)
    | false => escape c

partial def group : Parser Ast :=
  withErrorMessage "expected a group" do
    let _ ← token '('
    let nonCapturing ← test (chars "?:")
    let r ← regex
    let _ ← token ')'
    pure (if nonCapturing then r else .group r)

partial def charWithPerlClasses : Parser Ast :=
  withErrorMessage "expected a character" do
    escaped true <|> (Ast.char <$> tokenFilter (!specialCharacters.contains ·))

partial def char : Parser Ast :=
  withErrorMessage "expected a character" do
    Ast.char <$> (escaped false <|> tokenFilter (!specialCharacters.contains ·))

partial def class_ : Parser Class := do
  let cannotUsePerlClassInInterval :=
    throwUnexpectedWithMessage none "cannot use perl classes in intervals"

  let expectsChar (ast : Ast) : Parser Char :=
    match ast with
    | Ast.perl _ => cannotUsePerlClassInInterval
    | Ast.char c => pure c
    | _          => throwUnexpected

  let first ← charWithPerlClasses
  let isInterval ← test (token '-')

  if isInterval then
    let second ← charWithPerlClasses
    let f ← expectsChar first
    let s ← expectsChar second
    if h : f ≤ s
      then pure (Class.range f s h)
      else throwUnexpectedWithMessage none "invalid range"
  else
    match first with
    | Ast.perl p => pure (Class.perl p)
    | Ast.char c => pure (Class.single c)
    | _          => throwUnexpected

partial def classes : Parser Ast :=
  withErrorMessage "expected a character class" do
    let _         ← token '['
    let negated   ← test (token '^')
    let classes ← takeMany1 class_
    let _         ← token ']'
    pure $ Ast.classes { negated := negated, classes := classes }

partial def primitive : Parser Ast := withBacktracking group <|> classes <|> charWithPerlClasses

partial def repetition : Parser Ast :=
  withErrorMessage "expected a star" do
    let r ← primitive
    -- Eat repetition operators as many as possible
    foldl folder r repetitionOp
where
  repeatAux (ast accum : Ast) (n : Nat) : Ast :=
    if n == 0 then
      accum
    else
      repeatAux ast (Ast.concat ast accum) (n - 1)
  -- requires n > 0
  repeatAst (ast : Ast) (n : Nat) : Ast :=
    repeatAux ast ast (n - 1)
  folder (ast : Ast) : (Nat × Option Nat) → Ast
    -- special case for well-known repetitions
    | (0, some 1) => Ast.alternate ast Ast.empty
    | (0, none) => Ast.star ast
    | (1, none) => Ast.concat ast (Ast.star ast)
    -- r{min,}. min > 0 as (0, none) is already covered.
    | (min, none) => Ast.concat (repeatAst ast min) (Ast.star ast)
    -- r{0,max}
    | (0, some max) =>
      if max == 0 then
        Ast.empty
      else
        repeatAst (Ast.alternate ast Ast.empty) max
    -- r{min,max} (min > 0)
    | (min, some max) =>
      if min == max then
        repeatAst ast min
      else
        Ast.concat (repeatAst ast min) (repeatAst (Ast.alternate ast Ast.empty) (max - min))
  repetitionOp : Parser (Nat × Option Nat) := do
    if (← test (token '*')) then
      return (0, none)
    else if (← test (token '+')) then
      return (1, none)
    else if (← test (token '?')) then
      return (0, some 1)
    else if (← test (token '{')) then
      let min ← ASCII.parseNat
      let max ← do
        if (← test (token ',')) then
          option? ASCII.parseNat
        else
          pure (some min)
      let _ ← token '}'
      return (min, max)
    else
      throwUnexpected

partial def concat : Parser Ast :=
  withErrorMessage "expected a concatenation" do
    foldl1 Ast.concat repetition

partial def alternate : Parser Ast :=
  withErrorMessage "expected an alternation" do
    let init ← branch
    foldl Ast.alternate init (Char.char '|' *> branch)
where
  branch : Parser Ast := optionD Ast.epsilon concat

partial def regex : Parser Ast :=
  withErrorMessage "expected a regular expression" do
    alternate

end

def parse (input : String) : Except String Expr :=
  match (regex <* endOfInput).run input.toSubstring with
  | .ok _ r => .ok (Ast.group r).toRegex
  | .error _ e => .error (toString e)

@[export lean_regex_parse_or_panic]
def parse! (input : String) : Expr :=
  match parse input with
  | Except.ok r => r
  | Except.error e => panic! s!"Failed to parse a regex: {e}"

end Regex.Syntax.Parser
