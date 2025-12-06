import Regex.Regex.Captures
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (ValidPos ValidPosPlusOne Slice)
open Regex.Strategy (materializeRegexGroups)

namespace Regex.CapturedGroups

variable {haystack : String} {self : CapturedGroups haystack} {index : Nat} {slice : Slice}

theorem lt_of_get_some (h : self.get index = .some slice) :
  2 * index + 1 < self.buffer.size := by
  grind [get, Option.bind_eq_some_iff]

theorem get_eq_none_of_ge (h : 2 * index + 1 ≥ self.buffer.size) :
  self.get index = .none := by
  grind [get, Option.bind_eq_none_iff]

def materialize (self : CapturedGroups haystack) (groups : Data.CaptureGroups haystack) : Prop :=
  ∀ i p₁ p₂ le, (self.get i) = .some ⟨haystack, p₁, p₂, le⟩ ↔ materializeRegexGroups groups i = .some (p₁, p₂)

/--
`CapturedGroups` conforms to the spec if and only if:

- The start position is valid (i.e., in the range of the haystack)
- The slice starts after the start position
- There is a regex match spanning the slice
- The captured groups contains the slices corresponding to the capture groups in the regex match
  - In particular, the first group corresponds to the slice of the overall match
  - the last match wins in case the same group is captured multiple times
-/
def Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (startPos : ValidPosPlusOne haystack) (self : CapturedGroups haystack) : Prop :=
  ∃ isValid pos pos' le groups,
    startPos.asValidPos isValid ≤ pos ∧
    s.expr.Captures pos pos' groups ∧
    self.get 0 = .some ⟨haystack, pos, pos', le⟩ ∧
    self.materialize groups

end Regex.CapturedGroups

namespace Regex.Captures

variable {haystack : String} {self self' : Captures haystack} {captured : CapturedGroups haystack}

theorem regex_eq_of_next?_some (h : self.next? = .some (captured, self')) :
  self'.regex = self.regex := by
  grind [next?]

theorem captures_of_next?_some (h : self.next? = .some (captured, self')) (isr : self.regex.IsSearchRegex) :
  captured.Spec isr haystack self.currentPos := by
  unfold next? at h
  split at h
  next isValid =>
    split at h
    next => grind
    next buffer h' =>
      simp only [Option.pure_def] at h
      split at h
      next => grind
      next slice h'' =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        have ⟨pos, pos', groups, le, c, eqv, eq₀, eq₁⟩ := isr.captureNextBuf_soundness h' (by grind)
        refine ⟨isValid, pos, pos', c.le, groups, le, c, ?_, ?_⟩
        . simp [CapturedGroups.get, eq₀, Vector.getElem_eq_iff.mp eq₁] at h''
          grind
        . intro index p₁ p₂ le
          have hbufsize : captured.buffer.size = self.regex.maxTag + 1 := by grind
          if lt : 2 * index + 1 < self.regex.maxTag + 1 then
            simp [eqv.eq index lt p₁ p₂, CapturedGroups.get, ←h.1, Option.bind_eq_some_iff]
            grind
          else
            have : self.regex.maxTag ≤ 2 * index := by grind
            simp only [CapturedGroups.get_eq_none_of_ge (hbufsize ▸ Nat.ge_of_not_lt lt),
              reduceCtorEq, false_iff, ne_eq]
            intro eq
            have mem : index ∈ isr.expr.tags := Strategy.mem_tags_of_materializeRegexGroups_some c (by grind)
            grind
  next => simp at h

end Regex.Captures
