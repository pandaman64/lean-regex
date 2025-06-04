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
  buffer : Array (Option Pos)
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
  currentPos : Pos
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
        { self with currentPos := self.haystack.next self.currentPos }
    pure (groups, next)
  else
    throw ()

/--
Gets the number of remaining characters to process in the haystack string.

* `self`: The captures iterator
* Returns: The number of remaining positions
-/
def Captures.remaining (self : Captures) : Pos :=
  self.haystack.endPos + ⟨1⟩ - self.currentPos

theorem Captures.lt_next?_some {groups : CapturedGroups} {m m' : Captures} (h : m.next? = some (groups, m')) :
  m.currentPos.byteIdx < m'.currentPos.byteIdx := by
  unfold next? at h
  split at h <;> simp [Option.bind_eq_some_iff] at h
  have ⟨_, _, h⟩ := h
  have ⟨_, _, h⟩ := h
  split at h
  next h' => simp [←h, h']
  next =>
    simp [←h, String.next]
    have : (m.haystack.get m.currentPos).utf8Size > 0 := Char.utf8Size_pos _
    omega

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
  have h₁ : m.currentPos < m'.currentPos := lt_next?_some h
  have h₂ : m.currentPos < m.haystack.endPos + ⟨1⟩ := by
    simp [next?] at h
    split at h <;> try contradiction
    next le => exact Nat.add_le_add_right le 1
  exact Nat.sub_lt_sub_left h₂ h₁

theorem _root_.String.Pos.sizeOf_eq {p : Pos} : sizeOf p = 1 + p.byteIdx := rfl
theorem _root_.String.Pos.sizeOf_lt_iff {p p' : Pos} :
  sizeOf p < sizeOf p' ↔ p < p' := by
  simp [String.Pos.sizeOf_eq]

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  rw [String.Pos.sizeOf_lt_iff];
  exact Captures.next?_decreasing (by assumption))

instance : Stream Captures CapturedGroups := ⟨Captures.next?⟩

end Regex

/--
Creates a new `Captures` iterator for a regex pattern and input string.

* `regex`: The compiled regex pattern to use for matching
* `s`: The input string to search in
* Returns: A `Captures` iterator positioned at the start of the string
-/
def Regex.captures (regex : Regex) (s : String) : Captures :=
  { regex := regex, haystack := s, currentPos := 0 }
