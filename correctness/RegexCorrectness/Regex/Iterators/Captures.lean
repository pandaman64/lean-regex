import Regex.Regex.Iterators.Captures
import RegexCorrectness.Regex.Iterators.CapturedGroups

open String (Pos)
open Std.Iterators

namespace Regex.Captures

def Valid (self : Captures) : Prop :=
  self.regex.IsSearchRegex ∧ self.currentPos.ValidPlus self.haystack

theorem valid_yield_of_valid {self self' : Captures} {groups : CapturedGroups} (h : self.step = .yield self' groups)
  (v : self.Valid) :
  self'.Valid := by
  have ⟨hle, buffer, eq₁, eq₂, matched, eq₃, eq₄⟩ := step_yield self self' groups h
  have v' := v.2.valid_of_le hle
  have ⟨it, it', groups', eqs, le, c, eqv, eq₅, eq₆⟩ := v.1.captureNextBuf_soundness eq₁ v' (by simp)
  refine ⟨by simpa [eq₄] using v.1, ?_⟩
  . simp [eq₄]
    split
    next =>
      simp [eq₂, CapturedGroups.get, eq₅, eq₆] at eq₃
      simp [←eq₃]
      have vp : Pos.ValidPlus it.toString it'.pos := c.toString_eq ▸ c.validR.validPlus
      simp [↓eqs] at vp
      exact vp
    next => exact String.Pos.validPlus_of_next_valid v'

theorem spec_yield_of_valid_of_bufferSize_eq {self self' : Captures} {groups : CapturedGroups} (h : self.step = .yield self' groups)
  (v : self.Valid) (eqBufSize : self.bufferSize = self.regex.maxTag + 1) :
  groups.Spec v.1 self.haystack self.currentPos := by
  have ⟨hle, buffer, eq₁, eq₂, matched, eq₃, eq₄⟩ := step_yield self self' groups h
  have v' := v.2.valid_of_le hle
  have ⟨it, it', groups', eqs, le, c, eqv, eq₅, eq₆⟩ := v.1.captureNextBuf_soundness eq₁ v' (by simp)
  refine ⟨it, it', groups', by simp [↓eqs], le, c, ?_, ?_⟩
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
      omega

theorem valid_skip_of_valid {self self' : Captures} (h : self.step = .skip self') (v : self.Valid) :
  self'.Valid := by
  have ⟨hle, h⟩ := step_skip self self' h
  have v' := v.2.valid_of_le hle
  exact ⟨by simpa [h] using v.1, by simp [h, String.Pos.ValidPlus]⟩

namespace IterM

variable {m : Type → Type w} [Pure m] {it' it : IterM (α := Captures) m CapturedGroups} {out : CapturedGroups}

theorem valid_capturesM {re : Regex} (haystack : String) (m : Type → Type w) (bufferSize : Nat) (s : re.IsSearchRegex) :
  (re.capturesM haystack m bufferSize).internalState.Valid :=
  ⟨s, haystack.valid_mkIterator.validPlus⟩

theorem valid_of_isPlausibleSuccessorOf_of_valid (so : it'.IsPlausibleSuccessorOf it) (v : it.internalState.Valid) :
  it'.internalState.Valid := by
  obtain ⟨step, h, h'⟩ := so
  simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, IsPlausibleStep] at h'
  cases eq : it.internalState.step with
  | yield it' out =>
    simp [eq] at h'
    simp [h', IterStep.successor] at h
    simp [←h]
    exact valid_yield_of_valid eq v
  | skip it' =>
    simp [eq] at h'
    simp [h', IterStep.successor] at h
    simp [←h]
    exact valid_skip_of_valid eq v
  | done =>
    simp [eq] at h'
    simp [h', IterStep.successor] at h

theorem eq_withPos_of_isPlausibleSuccessorOf (so : it'.IsPlausibleSuccessorOf it) :
  ∃ pos, it'.internalState = it.internalState.withPos pos := by
  obtain ⟨step, h, h'⟩ := so
  simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, IsPlausibleStep] at h'
  cases eq : it.internalState.step with
  | yield it' out =>
    simp [eq] at h'
    simp [h', IterStep.successor] at h
    have ⟨_, _, _, _, _, _, eq₄⟩ := step_yield it.internalState it' out eq
    simp [←h, eq₄]
  | skip it' =>
    simp [eq] at h'
    simp [h', IterStep.successor] at h
    have ⟨_, h''⟩ := step_skip it.internalState it' eq
    simp [←h, h'']
  | done =>
    simp [eq] at h'
    simp [h', IterStep.successor] at h

theorem spec_of_isPlausibleOutput_of_valid_of_bufferSize_eq (o : it.IsPlausibleOutput out) (v : it.internalState.Valid)
  (eqBufSize : it.internalState.bufferSize = it.internalState.regex.maxTag + 1) :
  out.Spec v.1 it.internalState.haystack it.internalState.currentPos := by
  obtain ⟨it', h⟩ := o
  simp [IterM.IsPlausibleStep, Iterator.IsPlausibleStep, IsPlausibleStep] at h
  cases eq : it.internalState.step with
  | yield _ groups =>
    simp [eq] at h
    simp [h]
    exact spec_yield_of_valid_of_bufferSize_eq eq v eqBufSize
  | skip _ | done => simp [eq] at h

theorem spec_of_isPlausibleIndirectOutput_of_valid_of_bufferSize_eq (io : it.IsPlausibleIndirectOutput out) (v : it.internalState.Valid)
  (eqBufSize : it.internalState.bufferSize = it.internalState.regex.maxTag + 1) :
  ∃ startPos, out.Spec v.1 it.internalState.haystack startPos := by
  induction io with
  | @direct it out h => exact ⟨it.internalState.currentPos, spec_of_isPlausibleOutput_of_valid_of_bufferSize_eq h v eqBufSize⟩
  | @indirect it it' out so io ih =>
    have ih := ih (valid_of_isPlausibleSuccessorOf_of_valid so v)
    have ⟨pos, eq⟩ := eq_withPos_of_isPlausibleSuccessorOf so
    simp [eq] at ih
    exact ih eqBufSize

end IterM

namespace Iter

theorem valid_captures {re : Regex} (haystack : String) (bufferSize : Nat) (s : re.IsSearchRegex) :
  (re.captures haystack bufferSize).internalState.Valid :=
  IterM.valid_capturesM haystack Id bufferSize s

theorem spec_of_isPlausibleIndirectOutput_of_captures {re : Regex} (haystack : String) (s : re.IsSearchRegex)
  (io : (re.captures haystack).IsPlausibleIndirectOutput out) :
  ∃ startPos, out.Spec s haystack startPos := by
  have v : (re.captures haystack).internalState.Valid := valid_captures haystack (re.maxTag + 1) s
  have eqBufSize : (re.captures haystack).internalState.bufferSize = re.maxTag + 1 := rfl
  rw [Iter.isPlausibleIndirectOutput_iff_isPlausibleIndirectOutput_toIterM] at io
  exact IterM.spec_of_isPlausibleIndirectOutput_of_valid_of_bufferSize_eq io v eqBufSize

-- TODO: Iter.isPlausibleIndirectOutput_of_mem_toArray

end Iter

end Regex.Captures
