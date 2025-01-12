-- Unit tests for the regex parser.
import Regex.Syntax.Parser.Basic3

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

#guard parse "(a)" = .ok (.group (.char 'a'))
#guard parse "(?:a)" = .ok (.char 'a')

#guard parse "[abc]" = .ok (.classes ⟨false, #[.single 'a', .single 'b', .single 'c']⟩)
#guard parse "[^abc]" = .ok (.classes ⟨true, #[.single 'a', .single 'b', .single 'c']⟩)
#guard parse "[a-z]" = .ok (.classes ⟨false, #[.range 'a' 'z' (by decide)]⟩)
#guard parse r"[\da]" = .ok (.classes ⟨false, #[.perl ⟨false, .digit⟩, .single 'a']⟩)
#guard parse "[-]" = .ok (.classes ⟨false, #[.single '-']⟩)
#guard parse "[a-]" = .ok (.classes ⟨false, #[.single 'a', .single '-']⟩)
-- special characters are allowed in classes
#guard parse r"[(){}*+?|^$.\--]" = .ok (.classes ⟨false, #[
  '(', ')', '{', '}', '*', '+', '?', '|', '^', '$', '.', '-', '-'
].map .single⟩)

#guard parse "|" = .ok (.alternate .epsilon .epsilon)
#guard parse "a|" = .ok (.alternate (.char 'a') .epsilon)
#guard parse "|a" = .ok (.alternate .epsilon (.char 'a'))
#guard parse "a|b" = .ok (.alternate (.char 'a') (.char 'b'))
#guard parse "a|b|c" = .ok (.alternate (.alternate (.char 'a') (.char 'b')) (.char 'c'))
#guard parse "ab|cd(e|f)" = .ok (.alternate
  (.concat (.char 'a') (.char 'b'))
  (.concat (.concat (.char 'c') (.char 'd')) (.group (.alternate (.char 'e') (.char 'f')))))

#guard parse "a*b*c*" = .ok (.concat (.concat (.star (.char 'a')) (.star (.char 'b'))) (.star (.char 'c')))

end Regex.Syntax.Parser.Test
