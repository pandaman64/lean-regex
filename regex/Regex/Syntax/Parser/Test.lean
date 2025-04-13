-- Unit tests for the regex parser.
import Regex.Syntax.Parser.Basic

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

#guard parseAst "(a)" = .ok (.group (.char 'a'))
#guard parseAst "(?:a)" = .ok (.char 'a')

#guard parseAst "^" = .ok (.anchor .start)
#guard parseAst "$" = .ok (.anchor .eos)
#guard parseAst "^abc$" = .ok (.concat (.concat (.concat (.concat (.anchor .start) (.char 'a')) (.char 'b')) (.char 'c')) (.anchor .eos))

#guard parseAst "[abc]" = .ok (.classes ⟨false, #[.single 'a', .single 'b', .single 'c']⟩)
#guard parseAst "[^abc]" = .ok (.classes ⟨true, #[.single 'a', .single 'b', .single 'c']⟩)
#guard parseAst "[a-z]" = .ok (.classes ⟨false, #[.range 'a' 'z' (by decide)]⟩)
#guard parseAst r"[\da]" = .ok (.classes ⟨false, #[.perl ⟨false, .digit⟩, .single 'a']⟩)
#guard parseAst "[-]" = .ok (.classes ⟨false, #[.single '-']⟩)
#guard parseAst "[a-]" = .ok (.classes ⟨false, #[.single 'a', .single '-']⟩)
-- special characters are allowed in classes
#guard parseAst r"[(){}*+?|^$.\--]" = .ok (.classes ⟨false, #[
  '(', ')', '{', '}', '*', '+', '?', '|', '^', '$', '.', '-', '-'
].map .single⟩)

#guard parseAst "|" = .ok (.alternate .epsilon .epsilon)
#guard parseAst "a|" = .ok (.alternate (.char 'a') .epsilon)
#guard parseAst "|a" = .ok (.alternate .epsilon (.char 'a'))
#guard parseAst "a|b" = .ok (.alternate (.char 'a') (.char 'b'))
#guard parseAst "a|b|c" = .ok (.alternate (.alternate (.char 'a') (.char 'b')) (.char 'c'))
#guard parseAst "ab|cd(e|f)" = .ok (.alternate
  (.concat (.char 'a') (.char 'b'))
  (.concat (.concat (.char 'c') (.char 'd')) (.group (.alternate (.char 'e') (.char 'f')))))

#guard parseAst "a*b*c*" = .ok (.concat (.concat (.star (.char 'a')) (.star (.char 'b'))) (.star (.char 'c')))
#guard parseAst "a?" = .ok (.alternate (.char 'a') .epsilon)

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
