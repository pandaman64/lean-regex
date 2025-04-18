import Regex.Regex.Matches
import RegexCorrectness.Regex.Basic

set_option autoImplicit false

open String (Pos)

namespace Regex.Matches

/--
The pair of positions returned by `Matches` functions conforms to the spec if and only if:

- the haystack can be split into `l`, `m`, and `r` such that `haystack = l ++ m ++ r`
- there is a regex match starting at `l`, matching the substring `m`, and ending at `r`
- the first position corresponds to the start of the matched substring `m`
- the second position corresponds to the end of the matched substring `m`
-/
def Spec {re : Regex} (s : re.IsSearchRegex) (haystack : String) (positions : Pos × Pos) : Prop :=
  ∃ l m r groups,
    haystack = ⟨l ++ m ++ r⟩ ∧
    s.expr.Captures ⟨l, [], m ++ r⟩ ⟨l, m.reverse, r⟩ groups ∧
    positions.1 = ⟨String.utf8Len l⟩ ∧
    positions.2 = ⟨String.utf8Len l + String.utf8Len m⟩

def Valid (self : Matches) : Prop :=
  self.regex.IsSearchRegex ∧ self.currentPos.ValidPlus self.haystack

theorem captures_of_next?_some {self self' : Matches} {positions} (h : self.next? = .some (positions, self'))
  (v : self.Valid) (bt : ¬self.regex.useBacktracker) :
  self'.Valid ∧ Spec v.1 self.haystack positions := by
  unfold next? at h
  split at h
  next le =>
    have pos_valid := v.2.valid_of_le le
    simp [Regex.searchNext, bt] at h
    generalize h' : VM.searchNext self.regex.nfa self.regex.wf ⟨self.haystack, self.currentPos⟩ = matched at h
    match matched with
    | none => simp at h
    | some matched =>
      simp at h
      have ⟨l, m, r, groups, eqstring, c, eq₁, eq₂⟩ := v.1.searchNext_some h' pos_valid
      simp at eqstring
      split at h
      next =>
        simp at h
        simp [←h, Valid]
        have pos_valid' : Pos.Valid self.haystack matched.2 := by
          simp [eq₂]
          refine ⟨l ++ m, r, ?_, by simp⟩
          simp [eqstring]
        exact ⟨⟨v.1, String.Pos.validPlus_of_valid pos_valid'⟩, l, m, r, groups, by simp [eqstring], c, eq₁, eq₂⟩
      next =>
        simp at h
        simp [←h, Valid]
        exact ⟨⟨v.1, String.Pos.validPlus_of_next_valid pos_valid⟩, l, m, r, groups, by simp [eqstring], c, eq₁, eq₂⟩
  next => simp at h

theorem regex_eq_of_next?_some {self self' : Matches} {positions} (h : self.next? = .some (positions, self')) (bt : ¬self.regex.useBacktracker) :
  self'.regex = self.regex := by
  unfold next? at h
  split at h
  next =>
    simp [Regex.searchNext, bt] at h
    set matched := VM.searchNext self.regex.nfa self.regex.wf ⟨self.haystack, self.currentPos⟩
    match h' : matched with
    | none => simp at h
    | some matched =>
      simp at h
      split at h <;> simp at h <;> simp [←h]
  next => simp at h

theorem haystack_eq_of_next?_some {self self' : Matches} {positions} (h : self.next? = .some (positions, self')) (bt : ¬self.regex.useBacktracker) :
  self'.haystack = self.haystack := by
  unfold next? at h
  split at h
  next =>
    simp [Regex.searchNext, bt] at h
    set matched := VM.searchNext self.regex.nfa self.regex.wf ⟨self.haystack, self.currentPos⟩
    match h' : matched with
    | none => simp at h
    | some matched =>
      simp at h
      split at h <;> simp at h <;> simp [←h]
  next => simp at h

theorem vaild_matches {re : Regex} (haystack : String) (s : re.IsSearchRegex) :
  (re.matches haystack).Valid :=
  ⟨s, String.Pos.validPlus_of_valid haystack.valid_mkIterator⟩

end Regex.Matches
