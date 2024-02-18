import Parser
import Regex.Regex
import Regex.Parser.ParserAux

open Parser

namespace Regex.Parser

def specialCharacters := "[](){}*+?|^$.\\"

abbrev Parser := SimpleParser Substring Char

-- NOTE: I don't have any idea if the precedence or any other stuff are correct here
mutual

partial def paren : Parser Regex :=
  -- TODO: construct save node
  withErrorMessage "expected a paren" (token '(' *> regex <* token ')')

partial def char : Parser Regex :=
  withErrorMessage "expected a character" do
    let c ← tokenFilter (!specialCharacters.contains ·)
    pure (Regex.char c)

partial def primitive : Parser Regex := withBacktracking paren <|> char

partial def star : Parser Regex :=
  withErrorMessage "expected a star" do
    let r ← primitive
    optionD r (token '*' *> pure (Regex.star r))

partial def concat : Parser Regex :=
  withErrorMessage "expected a concatenation" do
    foldl1 Regex.concat star

partial def alternate : Parser Regex :=
  withErrorMessage "expected an alternation" do
    let init ← branch
    foldl Regex.alternate init (Char.char '|' *> branch)
where
  branch : Parser Regex := optionD Regex.epsilon concat

partial def regex : Parser Regex :=
  withErrorMessage "expected a regular expression" do
    alternate

end

def parse (input : String) : Except String Regex :=
  match (regex <* endOfInput).run input.toSubstring with
  | .ok _ r => .ok r
  | .error e => .error (toString e)

@[export lean_regex_parse_or_panic]
def parse! (input : String) : Regex :=
  match parse input with
  | Except.ok r => r
  | Except.error e => panic! s!"Failed to parse a regex: {e}"

end Regex.Parser
