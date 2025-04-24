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
  ∃ it it' groups,
    it.toString = haystack ∧
    s.expr.Captures it it' groups ∧
    positions.1 = it.pos ∧
    positions.2 = it'.pos

def Valid (self : Matches) : Prop :=
  self.regex.IsSearchRegex ∧ self.currentPos.ValidPlus self.haystack

theorem captures_of_next?_some {self self' : Matches} {positions} (h : self.next? = .some (positions, self'))
  (v : self.Valid) :
  self'.Valid ∧ Spec v.1 self.haystack positions := by
  unfold next? at h
  split at h
  next le =>
    have pos_valid := v.2.valid_of_le le
    match h' : self.regex.searchNext ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some matched =>
      simp [h'] at h
      have ⟨it, it', groups, eqstring, c, eq₁, eq₂⟩ := v.1.searchNext_some h' pos_valid
      simp at eqstring
      split at h
      next =>
        simp at h
        simp [←h, Valid]
        exact ⟨⟨v.1, eqstring ▸ eq₂ ▸ c.validR.validPlus⟩, it, it', groups, by simp [←eqstring]; exact c.toString_eq.symm, c, eq₁, eq₂⟩
      next =>
        simp at h
        simp [←h, Valid]
        exact ⟨⟨v.1, String.Pos.validPlus_of_next_valid pos_valid⟩, it, it', groups, by simp [←eqstring]; exact c.toString_eq.symm, c, eq₁, eq₂⟩
  next => simp at h

theorem regex_eq_of_next?_some {self self' : Matches} {positions} (h : self.next? = .some (positions, self')) :
  self'.regex = self.regex := by
  unfold next? at h
  split at h
  next =>
    match h' : self.regex.searchNext ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some matched =>
      simp [h'] at h
      split at h <;> simp at h <;> simp [←h]
  next => simp at h

theorem haystack_eq_of_next?_some {self self' : Matches} {positions} (h : self.next? = .some (positions, self')) :
  self'.haystack = self.haystack := by
  unfold next? at h
  split at h
  next =>
    match h' : self.regex.searchNext ⟨self.haystack, self.currentPos⟩ with
    | none => simp [h'] at h
    | some matched =>
      simp [h'] at h
      split at h <;> simp at h <;> simp [←h]
  next => simp at h

theorem vaild_matches {re : Regex} (haystack : String) (s : re.IsSearchRegex) :
  (re.matches haystack).Valid :=
  ⟨s, haystack.valid_mkIterator.validPlus⟩

end Regex.Matches
