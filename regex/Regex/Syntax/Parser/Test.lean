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

#eval parseAst "a{1,|bx"
#guard parseAst "a{1,|bx" = .error .expectedEof
#eval parseAst "("
#guard parseAst "(" = .error .expectedEof
#eval parseAst ")"
#guard parseAst ")" = .error .expectedEof
#eval parseAst "(abc"
#guard parseAst "(abc" = .error .expectedEof
#eval parseAst "abc)"
#guard parseAst "abc)" = .error .expectedEof
#eval parseAst "[abc"
#guard parseAst "[abc" = .error .expectedEof
#eval parseAst "abc]"
#guard parseAst "abc]" = .error .expectedEof
#eval parseAst "a{}"
#guard parseAst "a{}" = .error .expectedEof
#eval parseAst "a{,}"
#guard parseAst "a{,}" = .error .expectedEof
#eval parseAst "a{,5}"
#guard parseAst "a{,5}" = .error .expectedEof
#eval parseAst "a{-1}"
#guard parseAst "a{-1}" = .error .expectedEof
#eval parseAst "a{-1,5}"
#guard parseAst "a{-1,5}" = .error .expectedEof
#eval parseAst "a{10,5}"
#guard parseAst "a{10,5}" = .error .expectedEof
#eval parseAst "*a"
#guard parseAst "*a" = .error .expectedEof
#eval parseAst "+a"
#guard parseAst "+a" = .error .expectedEof
#eval parseAst "?a"
#guard parseAst "?a" = .error .expectedEof
#eval parseAst "|*"
#guard parseAst "|*" = .error .expectedEof
#eval parseAst "\\x"
#guard parseAst "\\x" = .error .expectedEof
#eval parseAst "\\u"
#guard parseAst "\\u" = .error .expectedEof
#eval parseAst "\\u12"
#guard parseAst "\\u12" = .error .expectedEof
#eval parseAst "\\u{}"
#guard parseAst "\\u{}" = .error .expectedEof
#eval parseAst "\\u{xyz}"
#guard parseAst "\\u{xyz}" = .error .expectedEof
#eval parseAst "[]"
#guard parseAst "[]" = .error .expectedEof
#eval parseAst "[^]"
#guard parseAst "[^]" = .error .expectedEof
#eval parseAst "a{1"
#guard parseAst "a{1" = .error .expectedEof
#eval parseAst "a{1,"
#guard parseAst "a{1," = .error .expectedEof
#eval parseAst "a{1,2"
#guard parseAst "a{1,2" = .error .expectedEof
#eval parseAst "a{,"
#guard parseAst "a{," = .error .expectedEof
#eval parseAst "a)"
#guard parseAst "a)" = .error .expectedEof
#eval parseAst "(?:"
#guard parseAst "(?:" = .error .expectedEof
#eval parseAst "(?:a"
#guard parseAst "(?:a" = .error .expectedEof
#eval parseAst "(?:"
#guard parseAst "(?:" = .error .expectedEof

end Regex.Syntax.Parser.Test
