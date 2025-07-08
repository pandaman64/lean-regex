import Regex.Regex.Iterators.Captures
import RegexCorrectness.Regex.Iterators.CapturedGroups

open String (Pos)

namespace Regex.Captures

def Valid (self : Captures) : Prop :=
  self.regex.IsSearchRegex ∧ self.bufferSize = self.regex.maxTag + 1 ∧ self.currentPos.ValidPlus self.haystack

theorem valid_of_yield_valid {self self' : Captures} {groups : CapturedGroups} (h : self.step = .yield self' groups)
  (v : self.Valid) :
  self'.Valid ∧ groups.Spec v.1 self.haystack self.currentPos := by
  have ⟨hle, buffer, eq₁, eq₂, matched, eq₃, eq₄⟩ := step_yield self self' groups h
  have v' := v.2.2.valid_of_le hle
  have ⟨it, it', groups', eqs, le, c, eqv, eq₅, eq₆⟩ := v.1.captureNextBuf_soundness eq₁ v' (by simp)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  . simpa [eq₄] using v.1
  . simpa [eq₄] using v.2.1
  . simp [eq₄]
    split
    next =>
      simp [eq₂, CapturedGroups.get, eq₅, eq₆] at eq₃
      simp [←eq₃]
      have vp : Pos.ValidPlus it.toString it'.pos := c.toString_eq ▸ c.validR.validPlus
      simp [↓eqs] at vp
      exact vp
    next => exact String.Pos.validPlus_of_next_valid v'
  . refine ⟨it, it', groups', by simp [↓eqs], le, c, ?_, ?_⟩
    . simp [eq₂, CapturedGroups.get, eq₅, eq₆]
    . intro i p₁ p₂
      if lt : 2 * i + 1 < max self.bufferSize 2 then
        have h := eqv.eq i lt p₁ p₂
        simp [h, eq₂, CapturedGroups.get, Option.bind_eq_some_iff, Vector.getElem_eq_iff]
      else
        have eqsize : groups.buffer.size = max self.bufferSize 2 := by
          simp [eq₂]
        have eq : groups.get i = .none := groups.get_eq_none_of_ge (Nat.ge_of_not_lt (eqsize ▸ lt))
        simp [eq]
        intro eq'
        have mem : i ∈ v.1.expr.tags := Strategy.mem_tags_of_materializeRegexGroups_some (tag := i) c (by simp [eq'])
        have lt' : 2 * i < self.regex.maxTag := v.1.maxTag_eq ▸ NFA.lt_of_mem_tags_compile v.1.nfa_eq.symm mem
        have eqBufSize : self.bufferSize = self.regex.maxTag + 1 := v.2.1
        omega

theorem valid_of_skip_valid {self self' : Captures} (h : self.step = .skip self') (v : self.Valid) :
  self'.Valid := by
  have ⟨hle, h⟩ := step_skip self self' h
  have v' := v.2.2.valid_of_le hle
  exact ⟨by simpa [h] using v.1, by simpa [h] using v.2.1, by simp [h, String.Pos.ValidPlus]⟩

theorem valid_captures {re : Regex} (haystack : String) (s : re.IsSearchRegex) :
  (re.captures haystack).internalState.Valid :=
  ⟨s, rfl, haystack.valid_mkIterator.validPlus⟩

end Regex.Captures
