import Regex.Regex.Captures
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (Pos)
open Regex.Strategy (materializeRegexGroups)

namespace Regex.CapturedGroups

theorem lt_of_get_some {self : CapturedGroups} {i s} (h : self.get i = .some s) :
  2 * i + 1 < self.buffer.size := by
  simp only [get, Option.pure_def, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq,
    ↓existsAndEq, true_and] at h
  have ⟨p₁, eq₁, p₂, eq₂, eqs⟩ := h
  simp only [Array.getElem?_eq_some_iff] at eq₂
  have ⟨lt, eq₂⟩ := eq₂
  exact lt

theorem get_eq_none_of_ge {self : CapturedGroups} {i} (h : 2 * i + 1 ≥ self.buffer.size) :
  self.get i = .none := by
  simp [get]
  intro p₁ eq₁ p₁' eq₁' p₂ eq₂ p₂' eq₂'
  simp [Array.getElem?_eq_some_iff] at eq₂
  have ⟨lt, eq₂⟩ := eq₂
  omega

def materialize (self : CapturedGroups) (groups : Data.CaptureGroups) : Prop :=
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
def Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (startPos : Pos.Raw) (self : CapturedGroups) : Prop :=
  ∃ it it' groups,
    it.toString = haystack ∧
    startPos ≤ it.pos ∧
    s.expr.Captures it it' groups ∧
    self.get 0 = .some ⟨haystack, it.pos, it'.pos⟩ ∧
    self.materialize groups

end Regex.CapturedGroups

namespace Regex.Captures

def Valid (self : Captures) : Prop :=
  self.regex.IsSearchRegex ∧ self.currentPos.ValidPlus self.haystack

theorem captures_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self'))
  (v : self.Valid) :
  self'.Valid ∧ captured.Spec v.1 self.haystack self.currentPos := by
  unfold next? at h
  split at h
  next le =>
    match h' : self.regex.captureNextBuf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some matched =>
      have pos_valid := v.2.valid_of_le le
      have : 1 ≤ self.regex.maxTag := v.1.le_maxTag
      have ⟨it, it', groups, eqs, le, c, eqv, eq₁, eq₂⟩ :=
        v.1.captureNextBuf_soundness h' pos_valid (by omega)
      simp at eqs

      simp [h'] at h
      set captured' : CapturedGroups := ⟨self.haystack, matched.toArray⟩
      have materializes : captured'.materialize groups := by
        intro i p₁ p₂
        have eqsize : matched.toArray.size = self.regex.maxTag + 1 := matched.size_toArray
        if lt : 2 * i + 1 < matched.toArray.size then
          have eq := eqv.eq i (by omega) p₁ p₂
          simp [eq, captured', CapturedGroups.get, Option.bind_eq_some_iff, Vector.getElem?_eq_some_iff]
          apply Iff.intro
          . intro ⟨⟨_, h₁⟩, ⟨_, h₂⟩⟩
            exact ⟨h₁, h₂⟩
          . intro ⟨h₁, h₂⟩
            exact ⟨⟨by omega, h₁⟩, ⟨by omega, h₂⟩⟩
        else
          have eq : captured'.get i = .none := captured'.get_eq_none_of_ge (Nat.ge_of_not_lt lt)
          simp [eq]
          intro eq'
          have mem : i ∈ v.1.expr.tags := Strategy.mem_tags_of_materializeRegexGroups_some (tag := i) c (by simp [eq'])
          have lt' : 2 * i < self.regex.maxTag := v.1.maxTag_eq ▸ NFA.lt_of_mem_tags_compile v.1.nfa_eq.symm mem
          omega

      have captured₀ : captured'.get 0 = .some ⟨self.haystack, it.pos, it'.pos⟩ := by
        have eq : materializeRegexGroups groups 0 = some (it.pos, it'.pos) := (eqv.eq 0 (by omega) it.pos it'.pos).mpr ⟨eq₁, eq₂⟩
        have eq' : captured'.get 0 = .some ⟨captured'.haystack, it.pos, it'.pos⟩ := (materializes 0 it.pos it'.pos).mpr eq
        simp [eq', captured']

      simp [captured₀] at h
      refine ⟨?_, it, it', groups, eqs, le, c, h.1 ▸ captured₀, h.1 ▸ materializes⟩
      split at h
      next =>
        simp [←h.2]
        have vp : Pos.Raw.ValidPlus it.toString it'.pos := c.toString_eq ▸ c.validR.validPlus
        exact ⟨v.1, eqs ▸ vp⟩
      next nlt =>
        simp [←h.2]
        exact ⟨v.1, String.Pos.Raw.validPlus_of_next_valid pos_valid⟩
  next => simp at h

theorem regex_eq_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self')) :
  self'.regex = self.regex := by
  unfold next? at h
  split at h
  next =>
    match h' : self.regex.captureNextBuf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some buffer =>
      simp [h', Option.bind_eq_some_iff] at h
      have ⟨_, _, _, h⟩ := h
      simp [←h]
      split <;> rfl
  next => simp at h

theorem haystack_eq_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self')) :
  self'.haystack = self.haystack := by
  unfold next? at h
  split at h
  next =>
    match h' : self.regex.captureNextBuf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some buffer =>
      simp [h', Option.bind_eq_some_iff] at h
      have ⟨_, _, _, h⟩ := h
      simp [←h]
      split <;> rfl
  next => simp at h

theorem valid_captures {re : Regex} (haystack : String) (s : re.IsSearchRegex) :
  (re.captures haystack).Valid :=
  ⟨s, haystack.valid_mkIterator.validPlus⟩

end Regex.Captures
