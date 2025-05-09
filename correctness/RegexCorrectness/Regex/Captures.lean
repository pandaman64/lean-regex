import Regex.Regex.Captures
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (Pos)
open Regex.Strategy (materializeRegexGroups)

/--
`CapturedGroups` conforms to the spec if and only if:

- the haystack can be split into `l`, `m`, and `r` such that `haystack = l ++ m ++ r`
- `m` starts after `startPos`.
- there is a regex match starting at `l`, matching the substring `m`, and ending at `r`
- `CapturedGroups` contains the positions of the capture groups in the match
  - in particular, the first group corresponds to the positions of the matched substring `m`
  - the last match of wins in case the same group is captured multiple times
-/
def Regex.CapturedGroups.Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (startPos : Pos) (self : CapturedGroups) : Prop :=
  ∃ it it' groups,
    it.toString = haystack ∧
    startPos ≤ it.pos ∧
    s.expr.Captures it it' groups ∧
    self.get 0 = .some (it.pos, it'.pos) ∧
    ∀ i, self.get i = materializeRegexGroups groups i

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
      set captured' := CapturedGroups.mk matched.toArray
      have hcaptured (i : Nat) : captured'.get i = materializeRegexGroups groups i := by
        have eqsize : matched.toArray.size = self.regex.maxTag + 1 :=
          matched.size_toArray
        if h₁ : 2 * i + 1 < self.regex.maxTag + 1 then
          match eq₁ : matched[2 * i]'(by omega) with
          | none =>
            have hgroup := (eqv i).1 (by omega)
            simp [eq₁] at hgroup
            have : matched.toArray[2 * i]? = .some .none :=
              eq₁ ▸ getElem?_pos matched.toArray (2 * i) (by omega)
            simp [CapturedGroups.get, this, hgroup, captured']
          | some v₁ =>
            match eq₂ : matched[2 * i + 1] with
            | none =>
              have hgroup := (eqv i).2 (by omega)
              simp [eq₂] at hgroup
              have : matched.toArray[2 * i + 1]? = .some .none :=
                eq₂ ▸ getElem?_pos matched.toArray (2 * i + 1) (by omega)
              simp [CapturedGroups.get, this, hgroup, captured']
            | some v₂ =>
              have hgroup₁ := (eqv i).1 (by omega)
              have hgroup₂ := (eqv i).2 (by omega)
              simp [eq₁, eq₂] at hgroup₁ hgroup₂
              have ⟨_, hgroup₁⟩ := hgroup₁
              have ⟨_, hgroup₂⟩ := hgroup₂
              simp [hgroup₁] at hgroup₂

              have eq₁' : matched.toArray[2 * i]? = .some v₁ :=
                eq₁ ▸ getElem?_pos matched.toArray (2 * i) (by omega)
              have eq₂' : matched.toArray[2 * i + 1]? = .some v₂ :=
                eq₂ ▸ getElem?_pos matched.toArray (2 * i + 1) (by omega)
              simp [CapturedGroups.get, eq₁', eq₂', hgroup₁, hgroup₂, captured']
        else
          match h₂ : materializeRegexGroups groups i with
          | none =>
            have : matched.toArray[2 * i + 1]? = .none :=
              getElem?_neg matched.toArray (2 * i + 1) (by omega)
            simp [CapturedGroups.get, this, captured']
          | some _ =>
            have : (materializeRegexGroups groups i).isSome := by simp [h₂]
            have := Strategy.mem_tags_of_materializeRegexGroups_some c this
            have := v.1.maxTag_eq ▸ NFA.lt_of_mem_tags_compile v.1.nfa_eq.symm this
            simp at h₁
            omega
      have captured₀ : captured'.get 0 = .some (it.pos, it'.pos) := by
        simp [hcaptured 0]
        have h₁ := (eqv 0).1 (by omega)
        have h₂ := (eqv 0).2 (by omega)
        simp [BufferStrategy] at eq₁ eq₂
        simp [eq₁] at h₁
        simp [eq₂] at h₂
        have ⟨_, eq₁⟩ := h₁
        have ⟨_, eq₂⟩ := h₂
        simp [eq₂] at eq₁
        simp [eq₁, eq₂]
      simp [captured₀] at h
      split at h
      next =>
        simp at h
        simp [←h, Valid]
        have vp : Pos.ValidPlus it.toString it'.pos := c.toString_eq ▸ c.validR.validPlus
        exact ⟨⟨v.1, eqs ▸ vp⟩, it, it', groups, eqs, le, c, captured₀, hcaptured⟩
      next nlt =>
        simp at h
        simp [←h, Valid]
        exact ⟨⟨v.1, String.Pos.validPlus_of_next_valid pos_valid⟩, it, it', groups, eqs, le, c, captured₀, hcaptured⟩
  next => simp at h

theorem regex_eq_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self')) :
  self'.regex = self.regex := by
  unfold next? at h
  split at h
  next =>
    match h' : self.regex.captureNextBuf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some buffer =>
      simp [h'] at h
      match h'' : CapturedGroups.get ⟨buffer.toArray⟩ 0 with
      | none => simp [h''] at h
      | some _ =>
        simp [h''] at h
        split at h
        next =>
          simp at h
          simp [←h]
        next =>
          simp at h
          simp [←h]
  next => simp at h

theorem haystack_eq_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self')) :
  self'.haystack = self.haystack := by
  unfold next? at h
  split at h
  next =>
    match h' : self.regex.captureNextBuf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some buffer =>
      simp [h'] at h
      match h'' : CapturedGroups.get ⟨buffer.toArray⟩ 0 with
      | none => simp [h''] at h
      | some _ =>
        simp [h''] at h
        split at h
        next =>
          simp at h
          simp [←h]
        next =>
          simp at h
          simp [←h]
  next => simp at h

theorem valid_captures {re : Regex} (haystack : String) (s : re.IsSearchRegex) :
  (re.captures haystack).Valid :=
  ⟨s, haystack.valid_mkIterator.validPlus⟩

end Regex.Captures
