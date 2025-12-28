-- match tests for the regex.
import Regex.Syntax.Parser.Basic
import Regex.NFA
import Regex.VM

namespace Regex.Syntax.Parser.Test

private def testMatch (pattern : String) (haystack : String) : Bool :=
  match parseAst pattern with
  | .error _ => false
  | .ok ast =>
    let expr := ast.toRegex
    let nfa := Regex.NFA.compile expr
    (Regex.VM.captureNextBuf nfa Regex.NFA.compile_wf 2 haystack.startPos).isSome

#guard testMatch "(?i)hello" "HELLO"
#guard testMatch "(?i)Σ" "Σ"
#guard testMatch "(?i)Σ" "σ"
#guard testMatch "(?i)Σ" "ς"
#guard testMatch "(?i)σ" "Σ"
#guard testMatch "(?i)σ" "σ"
#guard testMatch "(?i)σ" "ς"
#guard testMatch "(?i)ς" "Σ"
#guard testMatch "(?i)ς" "σ"
#guard testMatch "(?i)ς" "ς"

end Regex.Syntax.Parser.Test
