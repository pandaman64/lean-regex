import Regex.Regex.Matches
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (Pos PosPlusOne Slice)

namespace Regex.Matches

variable {haystack : String} {self self' : Matches haystack} {slice : Slice}

/--
The slice returned by `Matches` functions conforms to the spec if and only if:

- The start position is valid (i.e., in the range of the haystack)
- The slice starts after the start position
- There is a regex match spanning the slice
-/
def Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (startPos : PosPlusOne haystack) (slice : Slice) (eqs : slice.str = haystack) : Prop :=
  ∃ isValid pos pos' groups,
    startPos.asPos isValid ≤ pos ∧
    s.expr.Captures pos pos' groups ∧
    slice.startInclusive = eqs ▸ pos ∧
    slice.endExclusive = eqs ▸ pos'

theorem regex_eq_of_next?_some (h : self.next? = .some (slice, self')) :
  self'.regex = self.regex := by
  grind [next?]

theorem captures_of_next?_some (h : self.next? = .some (slice, self')) (isr : self.regex.IsSearchRegex) :
  Spec isr haystack self.currentPos slice (self.str_eq_of_next?_some h) := by
  unfold next? at h
  split at h
  next isValid =>
    split at h
    next => grind
    next slice' h' =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      have ⟨pos, pos', groups, le, c, eq₁, eq₂⟩ := isr.searchNext_some h'
      exact ⟨isValid, pos, pos', groups, le, c, h.1 ▸ eq₁, h.1 ▸ eq₂⟩
  next => simp at h

end Regex.Matches
