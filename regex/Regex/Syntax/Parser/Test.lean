-- Unit tests for the regex parser.
import Regex.Syntax.Parser.Basic
import Regex.Syntax.Parser.ToString

namespace Regex.Syntax.Parser.Test

private def decEq (a b : Except Error Ast) : Decidable (a = b) :=
  match a, b with
  | .ok a, .ok b =>
    if eq : a = b then
      isTrue (congrArg _ eq)
    else
      isFalse (by simp_all)
  | .error a, .error b =>
    if eq : a = b then
      isTrue (congrArg _ eq)
    else
      isFalse (by simp_all)
  | .ok _, .error _ => isFalse (by simp_all)
  | .error _, .ok _ => isFalse (by simp_all)

local instance : DecidableEq (Except Error Ast) := decEq

-- Helper function to test roundtrip: parse -> toString -> parse should equal original
private def testRoundtrip (input : String) (expected : Ast) : Bool :=
  match parseAst input with
  | .ok ast =>
    if ast = expected then
      match parseAst ast.toString with
      | .ok ast' => ast' = expected
      | .error _ => false
    else false
  | .error _ => false

#guard testRoundtrip "(a)" (.group (.char 'a'))
#guard testRoundtrip "(?:a)" (.char 'a')

#guard testRoundtrip "^" (.anchor .start)
#guard testRoundtrip "$" (.anchor .eos)
#guard testRoundtrip "^abc$" (.concat (.concat (.concat (.concat (.anchor .start) (.char 'a')) (.char 'b')) (.char 'c')) (.anchor .eos))

#guard testRoundtrip "[abc]" (.classes ⟨false, #[.single 'a', .single 'b', .single 'c']⟩)
#guard testRoundtrip "[^abc]" (.classes ⟨true, #[.single 'a', .single 'b', .single 'c']⟩)
#guard testRoundtrip "[a-z]" (.classes ⟨false, #[.range 'a' 'z' (by decide)]⟩)
#guard testRoundtrip r"[\da]" (.classes ⟨false, #[.perl ⟨false, .digit⟩, .single 'a']⟩)
#guard testRoundtrip "[-]" (.classes ⟨false, #[.single '-']⟩)
#guard testRoundtrip "[a-]" (.classes ⟨false, #[.single 'a', .single '-']⟩)
-- special characters are allowed in classes
#guard testRoundtrip r"[(){}*+?|^$.\--]" (.classes ⟨false, #[
  '(', ')', '{', '}', '*', '+', '?', '|', '^', '$', '.', '-', '-'
].map .single⟩)

#guard testRoundtrip "|" (.alternate .epsilon .epsilon)
#guard testRoundtrip "a|" (.alternate (.char 'a') .epsilon)
#guard testRoundtrip "|a" (.alternate .epsilon (.char 'a'))
#guard testRoundtrip "a|b" (.alternate (.char 'a') (.char 'b'))
#guard testRoundtrip "a|b|c" (.alternate (.alternate (.char 'a') (.char 'b')) (.char 'c'))
#guard testRoundtrip "ab|cd(e|f)" (.alternate
  (.concat (.char 'a') (.char 'b'))
  (.concat (.concat (.char 'c') (.char 'd')) (.group (.alternate (.char 'e') (.char 'f')))))

#guard testRoundtrip "a*b*c*" (.concat (.concat (.repeat 0 none (.char 'a')) (.repeat 0 none (.char 'b'))) (.repeat 0 none (.char 'c')))
#guard testRoundtrip "a?" (.repeat 0 (some 1) (.char 'a'))

-- escaping rules for special characters
#guard testRoundtrip "\\n" (.char '\n')
#guard testRoundtrip "\\t" (.char '\t')
#guard testRoundtrip "\\r" (.char '\r')
#guard testRoundtrip "\\a" (.char '\x07')
#guard testRoundtrip "\\f" (.char '\x0c')
#guard testRoundtrip "\\v" (.char '\x0b')
#guard testRoundtrip "\\0" (.char '\x00')
#guard testRoundtrip "\\-" (.char '-')
#guard testRoundtrip "\\[" (.char '[')
#guard testRoundtrip "\\]" (.char ']')
#guard testRoundtrip "\\(" (.char '(')
#guard testRoundtrip "\\)" (.char ')')
#guard testRoundtrip "\\{" (.char '{')
#guard testRoundtrip "\\}" (.char '}')
#guard testRoundtrip "\\*" (.char '*')
#guard testRoundtrip "\\+" (.char '+')
#guard testRoundtrip "\\?" (.char '?')
#guard testRoundtrip "\\|" (.char '|')
#guard testRoundtrip "\\^" (.char '^')
#guard testRoundtrip "\\$" (.char '$')
#guard testRoundtrip "\\." (.char '.')
#guard testRoundtrip "\\\\" (.char '\\')

#guard testRoundtrip "\\xab" (.char '\xab')
#guard testRoundtrip "\\u1234" (.char '\u1234')

#guard testRoundtrip "\\d" (.perl ⟨false, .digit⟩)
#guard testRoundtrip "\\D" (.perl ⟨true, .digit⟩)
#guard testRoundtrip "\\s" (.perl ⟨false, .space⟩)
#guard testRoundtrip "\\S" (.perl ⟨true, .space⟩)
#guard testRoundtrip "\\w" (.perl ⟨false, .word⟩)
#guard testRoundtrip "\\W" (.perl ⟨true, .word⟩)

#guard parseAst "\\z" = .error (.unexpectedEscapedChar 'z')
#guard parseAst "\\g" = .error (.unexpectedEscapedChar 'g')

-- '}' is not a special character
#guard testRoundtrip "}" (.char '}')

-- syntax errors and error messages
#guard parseAst "a{1,|bx" = .error (.unexpectedChar '|')
#guard parseAst "(" = .error .unexpectedEof
#guard parseAst ")" = .error .expectedEof
#guard parseAst "(abc" = .error .unexpectedEof
#guard parseAst "abc)" = .error .expectedEof
#guard parseAst "[abc" = .error .unexpectedEof
#guard parseAst "abc]" = .error .expectedEof
#guard parseAst "a{}" = .error (.unexpectedChar '}')
#guard parseAst "a{,}" = .error (.unexpectedChar ',')
#guard parseAst "a{,5}" = .error (.unexpectedChar ',')
#guard parseAst "a{-1}" = .error (.unexpectedChar '-')
#guard parseAst "a{-1,5}" = .error (.unexpectedChar '-')
#guard parseAst "a{10,5}" = .error .(.invalidRepetition 10 5)
#guard parseAst "*a" = .error .expectedEof
#guard parseAst "+a" = .error .expectedEof
#guard parseAst "?a" = .error .expectedEof
#guard parseAst "|*" = .error .expectedEof
#guard parseAst "\\x" = .error .unexpectedEof
#guard parseAst "\\u" = .error .unexpectedEof
#guard parseAst "\\u12" = .error .unexpectedEof
#guard parseAst "\\u{}" = .error (.unexpectedChar '{')
#guard parseAst "\\u{xyz}" = .error (.unexpectedChar '{')
#guard parseAst "[]" = .error (.unexpectedChar ']')
#guard parseAst "[^]" = .error (.unexpectedChar ']')
#guard parseAst "a{1" = .error .unexpectedEof
#guard parseAst "a{1," = .error .unexpectedEof
#guard parseAst "a{1,2" = .error .unexpectedEof
#guard parseAst "a{," = .error (.unexpectedChar ',')
#guard parseAst "a)" = .error .expectedEof
#guard parseAst "(?:" = .error .unexpectedEof
#guard parseAst "(?:a" = .error .unexpectedEof
#guard parseAst "(?:" = .error .unexpectedEof

-- We do not support \u{...} yet.
#guard parseAst "\\u{1234}" = .error (.unexpectedChar '{')

end Regex.Syntax.Parser.Test
