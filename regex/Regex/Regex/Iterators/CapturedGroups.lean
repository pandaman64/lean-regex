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
Returns the number of capture groups.

* `self`: The captured groups
* Returns: The number of capture groups
-/
def CapturedGroups.size (self : CapturedGroups) : Nat :=
  self.buffer.size / 2

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

end Regex
