-- import Regex.Regex.Captures
import Regex.Regex.Iterators.CapturedGroups
import RegexCorrectness.Regex.Basic

open Regex.Data (CaptureGroups)
open Regex.Strategy (materializeRegexGroups)
open String (Pos)

namespace Regex.CapturedGroups

theorem lt_of_get_some {self : CapturedGroups} {i s} (h : self.get i = .some s) :
  2 * i + 1 < self.buffer.size := by
  simp [get, Option.bind_eq_some_iff] at h
  have ⟨p₁, eq₁, p₁', eq₁', p₂, eq₂, p₂', eq₂', eq₃⟩ := h
  simp [Array.getElem?_eq_some_iff] at eq₂
  have ⟨lt, eq₂⟩ := eq₂
  exact lt

theorem get_eq_none_of_ge {self : CapturedGroups} {i} (h : 2 * i + 1 ≥ self.buffer.size) :
  self.get i = .none := by
  simp [get]
  intro p₁ eq₁ p₁' eq₁' p₂ eq₂ p₂' eq₂'
  simp [Array.getElem?_eq_some_iff] at eq₂
  have ⟨lt, eq₂⟩ := eq₂
  omega

def materialize (self : CapturedGroups) (groups : CaptureGroups) : Prop :=
  ∀ i p₁ p₂, (self.get i) = .some ⟨self.haystack, p₁, p₂⟩ ↔ materializeRegexGroups groups i = .some (p₁, p₂)

/--
`CapturedGroups` conforms to the spec if and only if:

- the haystack can be split into `l`, `m`, and `r` such that `haystack = l ++ m ++ r`
- `m` starts after `startPos`.
- there is a regex match starting at `l`, matching the substring `m`, and ending at `r`
- `CapturedGroups` contains the positions of the capture groups in the match
  - in particular, the first group corresponds to the positions of the matched substring `m`
  - the last match of wins in case the same group is captured multiple times
-/
def Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (startPos : Pos) (self : CapturedGroups) : Prop :=
  ∃ it it' groups,
    it.toString = haystack ∧
    startPos ≤ it.pos ∧
    s.expr.Captures it it' groups ∧
    self.get 0 = .some ⟨haystack, it.pos, it'.pos⟩ ∧
    self.materialize groups

end Regex.CapturedGroups
