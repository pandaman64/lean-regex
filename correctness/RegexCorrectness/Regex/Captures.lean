import Regex.Regex.Captures
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (Pos)

/--
`CapturedGroups` conforms to the spec if and only if:

- the haystack can be split into `l`, `m`, and `r` such that `haystack = l ++ m ++ r`
- there is a regex match starting at `l`, matching the substring `m`, and ending at `r`
- `CapturedGroups` contains the positions of the capture groups in the match
  - in particular, the first group corresponds to the positions of the matched substring `m`
  - the last match of wins in case the same group is captured multiple times
-/
def Regex.CapturedGroups.Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (self : CapturedGroups) : Prop :=
  ∃ l m r groups,
    haystack = ⟨l ++ m ++ r⟩ ∧
    s.expr.Captures ⟨l, [], m ++ r⟩ ⟨l, m.reverse, r⟩ groups ∧
    self.get 0 = .some (⟨String.utf8Len l⟩, ⟨String.utf8Len l + String.utf8Len m⟩) ∧
    ∀ i, self.get i = NFA.materializeRegexGroups groups i

namespace Regex.Captures

def Valid (self : Captures) : Prop :=
  self.regex.IsSearchRegex ∧ self.currentPos.Valid self.haystack

theorem captures_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self'))
  (v : self.Valid) :
  self'.Valid ∧ captured.Spec v.1 self.haystack := by
  unfold next? at h
  split at h
  next lt =>
    generalize h' : VM.captureNext self.regex.nfa self.regex.wf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ = matched at h
    match matched with
    | none => simp at h
    | some matched =>
      have : 1 ≤ self.regex.maxTag := v.1.le_maxTag
      have ⟨l, m, r, groups, eqstring, c, eqv, eq₁, eq₂⟩ :=
        v.1.captures_of_captureNext h' v.2 (by omega)
      simp at eqstring

      simp at h
      set captured' := CapturedGroups.mk matched.toArray
      have hcaptured (i : Nat) : captured'.get i = NFA.materializeRegexGroups groups i := by
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
          match h₂ : NFA.materializeRegexGroups groups i with
          | none =>
            have : matched.toArray[2 * i + 1]? = .none :=
              getElem?_neg matched.toArray (2 * i + 1) (by omega)
            simp [CapturedGroups.get, this, captured']
          | some _ =>
            have : (NFA.materializeRegexGroups groups i).isSome := by simp [h₂]
            have := NFA.mem_tags_of_materializeRegexGroups_some c this
            have := v.1.maxTag_eq ▸ NFA.lt_of_mem_tags_compile v.1.nfa_eq.symm this
            simp at h₁
            omega
      have captured₀ : captured'.get 0 = .some (⟨String.utf8Len l⟩, ⟨String.utf8Len l + String.utf8Len m⟩) := by
        simp [hcaptured 0]
        have h₁ := (eqv 0).1 (by omega)
        have h₂ := (eqv 0).2 (by omega)
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
        have vp : Pos.Valid self.haystack ⟨String.utf8Len l + String.utf8Len m⟩ := by
          refine ⟨l ++ m, r, ?_, by simp⟩
          simp [eqstring]
        exact ⟨⟨v.1, vp⟩, l, m, r, groups, by simp [eqstring], c, captured₀, hcaptured⟩
      next nlt =>
        simp at h
        simp [←h, Valid]
        exact ⟨⟨v.1, String.valid_next v.2 lt⟩, l, m, r, groups, by simp [eqstring], c, captured₀, hcaptured⟩
  next => simp at h

theorem regex_eq_of_next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self')) :
  self'.regex = self.regex := by
  unfold next? at h
  split at h
  next =>
    simp at h
    set captured' := VM.captureNext self.regex.nfa self.regex.wf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩
    match h' : captured' with
    | none => simp at h
    | some buffer =>
      simp at h
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
    simp at h
    set captured' := VM.captureNext self.regex.nfa self.regex.wf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩
    match h' : captured' with
    | none => simp at h
    | some buffer =>
      simp at h
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
  ⟨s, haystack.valid_mkIterator⟩

end Regex.Captures
