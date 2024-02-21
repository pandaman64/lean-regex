import Parser
import Regex.Regex
import Regex.Parser.Hir
import Regex.Parser.ParserAux

open Parser

namespace Regex.Parser

def specialCharacters := "[](){}*+?|^$.\\"

abbrev Parser := SimpleParser Substring Char

-- NOTE: I don't have any idea if the precedence or any other stuff are correct here
mutual

partial def group : Parser Hir :=
  withErrorMessage "expected a group" (token '(' *> Hir.group <$> regex <* token ')')

partial def char : Parser Hir :=
  withErrorMessage "expected a character" do
    let c ← tokenFilter (!specialCharacters.contains ·)
    pure (Hir.char c)

partial def primitive : Parser Hir := withBacktracking group <|> char

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
  | .ok _ r => .ok r.toRegex
  | .error e => .error (toString e)

@[export lean_regex_parse_or_panic]
def parse! (input : String) : Regex :=
  match parse input with
  | Except.ok r => r
  | Except.error e => panic! s!"Failed to parse a regex: {e}"

end Regex.Parser
