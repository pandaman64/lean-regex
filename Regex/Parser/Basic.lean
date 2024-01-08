import Parser
import Regex.Regex
import Regex.Parser.ParserAux

open Parser

namespace Regex.Parser

def specialCharacters := "[](){}*+?|^$.\\"

abbrev Parser := SimpleParser Substring Char

def char : Parser Regex :=
  withErrorMessage "expected a character" do
    let c ← tokenFilter (!specialCharacters.contains ·)
    pure (Regex.char c)

def concat : Parser Regex :=
  withErrorMessage "expected a concatenation" do
    foldl1 Regex.concat char

def alternate : Parser Regex :=
  withErrorMessage "expected an alternation" do
    let init ← branch
    foldl Regex.alternate init (Char.char '|' *> branch)
where
  branch : Parser Regex := optionD Regex.epsilon concat

def regex : Parser Regex :=
  withErrorMessage "expected a regular expression" do
    alternate

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
