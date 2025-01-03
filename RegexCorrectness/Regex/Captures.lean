import Regex.Regex.Captures
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

namespace Regex.Captures

def Valid (self : Captures) : Prop :=
  self.regex.IsSearchRegex ∧ self.currentPos.Valid self.haystack

theorem next?_some {self self' : Captures} {captured} (h : self.next? = .some (captured, self'))
  (v : self.Valid) :
  self'.Valid ∧
  ∃ l m r groups,
    v.1.expr.Captures ⟨l, [], m ++ r⟩ ⟨l, m.reverse, r⟩ groups ∧
    ∀ i, captured.get i = NFA.materializeRegexGroups groups i := by
  unfold next? at h
  split at h
  next lt =>
    generalize h' : VM.captureNext self.regex.nfa self.regex.wf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩ = matched at h
    match matched with
    | none => simp at h
    | some matched =>
      have : 1 ≤ self.regex.maxTag := v.1.le_maxTag
      have ⟨l, m, r, groups, c, eqv, eq₁, eq₂⟩ := v.1.captures_of_captureNext h' v.2 (by omega)

      simp at h
      set captured' := CapturedGroups.mk matched.val
      have hcaptured (i : Nat) : captured'.get i = NFA.materializeRegexGroups groups i := by
        have eqsize : matched.val.size = self.regex.maxTag + 1 :=
          matched.property
        if h₁ : 2 * i + 1 < self.regex.maxTag + 1 then
          match eq₁ : matched[2 * i]'(by omega) with
          | none =>
            have hgroup := (eqv i).1 (by omega)
            simp [eq₁] at hgroup
            have : matched.val[2 * i]? = .some .none :=
              eq₁ ▸ getElem?_pos matched.val (2 * i) (by omega)
            simp [CapturedGroups.get, this, hgroup]
          | some v₁ =>
            match eq₂ : matched[2 * i + 1] with
            | none =>
              have hgroup := (eqv i).2 (by omega)
              simp [eq₂] at hgroup
              have : matched.val[2 * i + 1]? = .some .none :=
                eq₂ ▸ getElem?_pos matched.val (2 * i + 1) (by omega)
              simp [CapturedGroups.get, this, hgroup]
            | some v₂ =>
              have hgroup₁ := (eqv i).1 (by omega)
              have hgroup₂ := (eqv i).2 (by omega)
              simp [eq₁, eq₂] at hgroup₁ hgroup₂
              have ⟨_, hgroup₁⟩ := hgroup₁
              have ⟨_, hgroup₂⟩ := hgroup₂
              simp [hgroup₁] at hgroup₂

              have eq₁' : matched.val[2 * i]? = .some v₁ :=
                eq₁ ▸ getElem?_pos matched.val (2 * i) (by omega)
              have eq₂' : matched.val[2 * i + 1]? = .some v₂ :=
                eq₂ ▸ getElem?_pos matched.val (2 * i + 1) (by omega)
              simp [CapturedGroups.get, eq₁', eq₂', hgroup₁, hgroup₂]
        else
          match h₂ : NFA.materializeRegexGroups groups i with
          | none =>
            have : matched.val[2 * i + 1]? = .none :=
              getElem?_neg matched.val (2 * i + 1) (by omega)
            simp [CapturedGroups.get, this]
          | some _ =>
            have : (NFA.materializeRegexGroups groups i).isSome := by simp [h₂]
            have := NFA.mem_tags_of_materializeRegexGroups_some c this
            have := v.1.maxTag_eq ▸ NFA.lt_of_mem_tags_compile v.1.nfa_eq.symm this
            simp at h₁
            omega
      have : captured'.get 0 = .some (⟨String.utf8Len l⟩, ⟨String.utf8Len l + String.utf8Len m⟩) := by
        simp [hcaptured 0]
        have h₁ := (eqv 0).1 (by omega)
        have h₂ := (eqv 0).2 (by omega)
        simp [eq₁] at h₁
        simp [eq₂] at h₂
        have ⟨_, eq₁⟩ := h₁
        have ⟨_, eq₂⟩ := h₂
        simp [eq₂] at eq₁
        simp [eq₁, eq₂]
      simp [this] at h
      split at h
      next =>
        simp at h
        simp [←h, Valid]
        -- TODO: requires `self.haystack = l ++ m ++ r` so that the position `⟨l ++ m⟩` is valid
        exact ⟨⟨v.1, sorry⟩, l, m, r, groups, c, hcaptured⟩
      next nlt =>
        simp at h
        simp [←h, Valid]
        exact ⟨⟨v.1, String.valid_next v.2 lt⟩, l, m, r, groups, c, hcaptured⟩
  next => simp at h

end Regex.Captures
