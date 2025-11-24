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
  currentPos : Pos.Raw
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
        { self with currentPos := self.currentPos.next self.haystack }
    pure (s, next)
  else
    throw ()

/--
Gets the number of remaining characters to process in the haystack string.

* `self`: The matches iterator
* Returns: The number of remaining positions
-/
def Matches.remaining (self : Matches) : Nat :=
  self.haystack.endPos.byteIdx + 1 - self.currentPos.byteIdx

theorem Matches.lt_next?_some {s : Substring} {m m' : Matches} (h : m.next? = some (s, m')) :
  m.currentPos.byteIdx < m'.currentPos.byteIdx := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  split at h
  next h' => simpa [←h] using h'
  next => simpa [←h, Pos.Raw.next] using Char.utf8Size_pos _

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
  have h₁ : m.currentPos.byteIdx < m'.currentPos.byteIdx := lt_next?_some h
  have h₂ : m.currentPos.byteIdx ≤ m.haystack.endPos.byteIdx := by
    unfold next? at h
    split at h
    next le => exact le
    next => simp at h
  grind

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  exact Matches.next?_decreasing (by assumption))

instance : Std.Stream Matches Substring := ⟨Matches.next?⟩

end Regex

/--
Creates a new `Matches` iterator for a regex pattern and input string.

* `regex`: The compiled regex pattern to use for matching
* `s`: The input string to search in
* Returns: A `Matches` iterator positioned at the start of the string
-/
def Regex.matches (regex : Regex) (s : String) : Matches :=
  { regex := regex, haystack := s, currentPos := 0 }
