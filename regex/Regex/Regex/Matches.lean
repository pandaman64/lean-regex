import Regex.Regex.Basic

set_option autoImplicit false

open String (Pos)

namespace Regex

/--
A structure that enables iterating through all matches of a regex pattern in a string.

Provides a stateful iterator for finding all regex matches in a haystack string.
-/
structure Matches where
  regex : Regex
  haystack : String
  currentPos : Pos
deriving Repr

/--
Gets the next match in the input string.

* `self`: The matches iterator
* Returns: An optional pair containing the matched substring and an updated iterator,
          or `none` if no more matches are found
-/
def Matches.next? (self : Matches) : Option (Substring × Matches) := do
  if self.currentPos ≤ self.haystack.endPos then
    let s ← self.regex.searchNext ⟨self.haystack, self.currentPos⟩
    let next :=
      if self.currentPos < s.stopPos then
        { self with currentPos := s.stopPos }
      else
        { self with currentPos := self.haystack.next self.currentPos }
    pure (s, next)
  else
    throw ()

/--
Gets the number of remaining characters to process in the haystack string.

* `self`: The matches iterator
* Returns: The number of remaining positions
-/
def Matches.remaining (self : Matches) : Pos :=
  self.haystack.endPos + ⟨1⟩ - self.currentPos

theorem Matches.lt_next?_some {s : Substring} {m m' : Matches} (h : m.next? = some (s, m')) :
  m.currentPos < m'.currentPos := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  split at h
  next h' => simp [←h, h']
  next =>
    simp [←h, String.next]
    have : (m.haystack.get m.currentPos).utf8Size > 0 := Char.utf8Size_pos _
    omega

theorem Matches.haystack_eq_next?_some {s : Substring} {m m' : Matches} (h : m.next? = some (s, m')) :
  m'.haystack = m.haystack := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  split at h <;> simp [←h]

theorem Matches.next?_decreasing {s : Substring} {m m' : Matches} (h : m.next? = some (s, m')) :
  m'.remaining < m.remaining := by
  unfold remaining
  rw [haystack_eq_next?_some h]
  have h₁ : m.currentPos < m'.currentPos := lt_next?_some h
  have h₂ : m.currentPos < m.haystack.endPos + ⟨1⟩ := by
    simp only [next?, String.pos_lt_eq, Option.pure_def, Option.bind_eq_bind] at h
    split at h <;> try contradiction
    next le => exact Nat.add_le_add_right le 1
  exact Nat.sub_lt_sub_left h₂ h₁

theorem _root_.String.Pos.sizeOf_eq {p : Pos} : sizeOf p = 1 + p.byteIdx := rfl
theorem _root_.String.Pos.sizeOf_lt_iff {p p' : Pos} :
  sizeOf p < sizeOf p' ↔ p < p' := by
  simp [String.Pos.sizeOf_eq]

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  rw [String.Pos.sizeOf_lt_iff];
  exact Matches.next?_decreasing (by assumption))

instance : Stream Matches Substring := ⟨Matches.next?⟩

end Regex

/--
Creates a new `Matches` iterator for a regex pattern and input string.

* `regex`: The compiled regex pattern to use for matching
* `s`: The input string to search in
* Returns: A `Matches` iterator positioned at the start of the string
-/
def Regex.matches (regex : Regex) (s : String) : Matches :=
  { regex := regex, haystack := s, currentPos := 0 }
