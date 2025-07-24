import Regex.Regex.Iterators.Matches
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (Pos Iterator)

namespace Regex.Matches

/--
The pair of positions returned by `Matches` functions conforms to the spec if and only if:

- the haystack can be split into `l`, `m`, and `r` such that `haystack = l ++ m ++ r`
- `m` starts after `startPos`.
- there is a regex match starting at `l`, matching the substring `m`, and ending at `r`
- the returned substring corresponds to `m`.
-/
def Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (startPos : Pos) (str : Substring) : Prop :=
  ∃ it it' groups,
    it.toString = haystack ∧
    startPos ≤ it.pos ∧
    s.expr.Captures it it' groups ∧
    str = ⟨haystack, it.pos, it'.pos⟩

-- TODO: IsPlausibleIndirectOutput for filterMap
-- theorem spec_of_isPlausibleIndirectOutput_of_matches {re : Regex} (haystack : String) (str : Substring) (s : re.IsSearchRegex)
--   (io : (re.matches haystack).IsPlausibleIndirectOutput str) :
--   ∃ startPos, Spec s haystack startPos str := by
--   sorry

end Regex.Matches
