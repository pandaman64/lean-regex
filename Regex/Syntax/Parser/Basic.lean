import Parser
import Regex.Regex
import Regex.Syntax.Hir
import Regex.Syntax.Parser.ParserAux

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

partial def escaped (withPerlClasses: Bool) : Parser (if withPerlClasses then Hir else Char) :=
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

    let perlClasses (c: Char) : Parser Hir :=
      match c with
      | 'd' => pure (Hir.perl (PerlClass.mk false PerlClassKind.digit))
      | 'D' => pure (Hir.perl (PerlClass.mk true PerlClassKind.digit))
      | 's' => pure (Hir.perl (PerlClass.mk false PerlClassKind.space))
      | 'S' => pure (Hir.perl (PerlClass.mk true PerlClassKind.space))
      | 'w' => pure (Hir.perl (PerlClass.mk false PerlClassKind.word))
      | 'W' => pure (Hir.perl (PerlClass.mk true PerlClassKind.word))
      |  _  => throwUnexpected

    match withPerlClasses with
    | true  => perlClasses c <|> (Hir.char <$> escape c)
    | false => escape c

partial def group : Parser Hir :=
  withErrorMessage "expected a group" do
    let _ ← token '('
    let nonCapturing ← test (chars "?:")
    let r ← regex
    let _ ← token ')'
    pure (if nonCapturing then r else .group r)

partial def charWithPerlClasses : Parser Hir :=
  withErrorMessage "expected a character" do
    escaped true <|> (Hir.char <$> tokenFilter (!specialCharacters.contains ·))

partial def char : Parser Hir :=
  withErrorMessage "expected a character" do
    Hir.char <$> (escaped false <|> tokenFilter (!specialCharacters.contains ·))

partial def interval : Parser Interval := do
  let cannotUsePerlClassInInterval :=
    throwUnexpectedWithMessage none "cannot use perl classes in intervals"

  let expectsChar (hir: Hir) : Parser Char :=
    match hir with
    | Hir.perl _ => cannotUsePerlClassInInterval
    | Hir.char c => pure c
    | _          => throwUnexpected

  let first ← charWithPerlClasses
  let isInterval ← test (token '-')

  if isInterval then
    let second ← charWithPerlClasses
    let f ← expectsChar first
    let s ← expectsChar second
    if h : f ≤ s
      then pure (Interval.range f s h)
      else throwUnexpectedWithMessage none "invalid range"
  else
    match first with
    | Hir.perl p => pure (Interval.perl p)
    | Hir.char c => pure (Interval.single c)
    | _          => throwUnexpected

partial def classes : Parser Hir :=
  withErrorMessage "expected a character class" do
    let _         ← token '['
    let negated   ← test (token '^')
    let intervals ← takeMany1 interval
    let _         ← token ']'
    pure $ Hir.classes { negated := negated, intervals := intervals }

partial def primitive : Parser Hir := withBacktracking group <|> classes <|> charWithPerlClasses

partial def star : Parser Hir :=
  withErrorMessage "expected a star" do
    let r ← primitive
    -- Eat stars as many as possible
    foldl (fun r _ => Hir.star r) r (token '*')

partial def concat : Parser Hir :=
  withErrorMessage "expected a concatenation" do
    foldl1 Hir.concat star

partial def alternate : Parser Hir :=
  withErrorMessage "expected an alternation" do
    let init ← branch
    foldl Hir.alternate init (Char.char '|' *> branch)
where
  branch : Parser Hir := optionD Hir.epsilon concat

partial def regex : Parser Hir :=
  withErrorMessage "expected a regular expression" do
    alternate

end

def parse (input : String) : Except String Regex :=
  match (regex <* endOfInput).run input.toSubstring with
  | .ok _ r => .ok (Hir.group r).toRegex
  | .error e => .error (toString e)

@[export lean_regex_parse_or_panic]
def parse! (input : String) : Regex :=
  match parse input with
  | Except.ok r => r
  | Except.error e => panic! s!"Failed to parse a regex: {e}"

end Regex.Syntax.Parser
