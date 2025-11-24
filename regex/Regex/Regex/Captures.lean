import Regex.Regex.Basic

set_option autoImplicit false

open String (Pos)

namespace Regex

/--
A structure representing the capture groups from a regex match.

Contains the original string (haystack) and a buffer of positions marking
the start and end of each capture group.
-/
structure CapturedGroups where
  haystack : String
  buffer : Array (Option Pos.Raw)
deriving Repr, DecidableEq, Inhabited

/--
Gets a specific capture group as a substring.

* `self`: The captured groups
* `index`: The index of the capture group to retrieve (0 for the entire match)
* Returns: An optional substring representing the capture group, or `none` if the group didn't participate in the match
-/
def CapturedGroups.get (self : CapturedGroups) (index : Nat) : Option Substring := do
  let start ← (← self.buffer[2 * index]?)
  let stop ← (← self.buffer[2 * index + 1]?)
  return ⟨self.haystack, start, stop⟩

/--
Converts all capture groups to an array of optional substrings.

* `self`: The captured groups
* Returns: An array where each element is either a substring for a capture group
          or `none` if that group didn't participate in the match
-/
def CapturedGroups.toArray (self : CapturedGroups) : Array (Option Substring) :=
  go 0 #[]
where
  go (i : Nat) (accum : Array (Option Substring)) : Array (Option Substring) :=
    if 2 * i < self.buffer.size then
      go (i + 1) (accum.push (self.get i))
    else
      accum

/--
A structure that enables iterating through all capture groups of regex matches in a string.

Provides a stateful iterator for finding all regex matches and their capture groups
in a haystack string.
-/
structure Captures where
  regex : Regex
  haystack : String
  currentPos : Pos.Raw
deriving Repr

/--
Gets the next match and its capture groups.

* `self`: The captures iterator
* Returns: An optional pair containing the captured groups and an updated iterator,
          or `none` if no more matches are found
-/
def Captures.next? (self : Captures) : Option (CapturedGroups × Captures) := do
  if self.currentPos ≤ self.haystack.endPos then
    let buffer ← self.regex.captureNextBuf (self.regex.maxTag + 1) ⟨self.haystack, self.currentPos⟩
    let groups : CapturedGroups := ⟨self.haystack, buffer.toArray⟩
    let s ← groups.get 0
    let next :=
      if self.currentPos < s.stopPos then
        { self with currentPos := s.stopPos }
      else
        { self with currentPos := self.currentPos.next self.haystack }
    pure (groups, next)
  else
    throw ()

theorem Captures.zeroth_group_some_of_next?_some {self next : Captures} {groups : CapturedGroups}
    (h : self.next? = (groups,next)) : groups.get 0 |>.isSome := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  have ⟨_, h, ⟨h', _⟩⟩ := h
  rw [h'] at h
  exact Option.isSome_of_mem h

/--
Gets the number of remaining characters to process in the haystack string.

* `self`: The captures iterator
* Returns: The number of remaining positions
-/
def Captures.remaining (self : Captures) : Nat :=
  self.haystack.endPos.byteIdx + 1 - self.currentPos.byteIdx

theorem Captures.lt_next?_some {groups : CapturedGroups} {m m' : Captures} (h : m.next? = some (groups, m')) :
  m.currentPos.byteIdx < m'.currentPos.byteIdx := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  have ⟨_, _, h⟩ := h
  split at h
  next h' => simpa [←h] using h'
  next => simpa [←h, Pos.Raw.next] using Char.utf8Size_pos _

theorem Captures.haystack_eq_next?_some {groups : CapturedGroups} {m m' : Captures} (h : m.next? = some (groups, m')) :
  m'.haystack = m.haystack := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  have ⟨_, _, h⟩ := h
  split at h <;> simp [←h]

theorem Captures.next?_decreasing {groups : CapturedGroups} {m m' : Captures} (h : m.next? = some (groups, m')) :
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
  exact Captures.next?_decreasing (by assumption))

instance : Std.Stream Captures CapturedGroups := ⟨Captures.next?⟩

end Regex

/--
Creates a new `Captures` iterator for a regex pattern and input string.

* `regex`: The compiled regex pattern to use for matching
* `s`: The input string to search in
* Returns: A `Captures` iterator positioned at the start of the string
-/
def Regex.captures (regex : Regex) (s : String) : Captures :=
  { regex := regex, haystack := s, currentPos := 0 }
