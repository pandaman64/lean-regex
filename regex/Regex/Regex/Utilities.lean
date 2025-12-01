import Regex.Regex.Matches
import Regex.Regex.Captures

open String (ValidPos Slice)

namespace Regex

/--
Finds the first match of a regex pattern in a string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An optional substring representing the match, or `none` if no match is found
-/
def find (regex : Regex) (haystack : String) : Option Slice :=
  regex.matches haystack |>.next? |>.map Prod.fst

/--
Finds all matches of a regex pattern in a string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An array of all matched substrings
-/
def findAll (regex : Regex) (haystack : String) : Array Slice :=
  go (regex.matches haystack) #[]
where
  go (m : Matches haystack) (accum : Array Slice) : Array Slice :=
    match _h : m.next? with
    | some (pos, m') => go m' (accum.push pos)
    | none => accum
  termination_by m

/--
Transforms the first match of a regex pattern using its capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `transformer`: The rule yielding the string to replace the match with
* Returns: The modified string, or the original string if no match is found
-/
def transform (regex : Regex) (haystack : String) (transformer : CapturedGroups haystack → String) : String :=
    match h : (regex.captures haystack).next? with
  | some (g, _) =>
    match h' : g.get 0, Captures.zeroth_group_some_of_next?_some h with
    | some s, _ =>
      have eq : s.str = haystack := CapturedGroups.get_str_eq_some h'
      ValidPos.extract haystack.startValidPos (s.startInclusive.cast eq) ++ transformer g ++ ValidPos.extract (s.endExclusive.cast eq) haystack.endValidPos
  | none => haystack

/--
Transforms all matches of a regex pattern using its capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `transformer`: The rule yielding the string to replace the match with
* Returns: The modified string, or the original string if no matches are found
-/
def transformAll (regex : Regex) (haystack : String) (transformer : CapturedGroups haystack → String) : String :=
  go (regex.captures haystack) "" haystack.startValidPos
where
  go (c : Captures haystack) (accum : String) (endPos : ValidPos haystack) : String :=
    match h : c.next? with
    | some (g, c') =>
      match h' : g.get 0, Captures.zeroth_group_some_of_next?_some h with
      | some s, _ =>
        have eq : s.str = haystack := CapturedGroups.get_str_eq_some h'
        go c' (accum ++ ValidPos.extract endPos (s.startInclusive.cast eq) ++ transformer g) (s.endExclusive.cast eq)
    | none =>
      accum ++ ValidPos.extract endPos haystack.endValidPos
  termination_by c

/--
Replaces the first match of a regex pattern with a replacement string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `replacement`: The string to replace the match with
* Returns: The modified string, or the original string if no match is found
-/
def replace (regex : Regex) (haystack : String) (replacement : String) : String :=
  transform regex haystack (fun _ => replacement)

/--
Replaces all matches of a regex pattern with a replacement string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `replacement`: The string to replace the matches with
* Returns: The modified string, or the original string if no matches are found
-/
def replaceAll (regex : Regex) (haystack : String) (replacement : String) : String :=
  transformAll regex haystack (fun _ => replacement)

/--
Captures the first match of a regex pattern in a string, including capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An optional `CapturedGroups` containing the match and its capture groups,
          or `none` if no match is found
-/
def capture (regex : Regex) (haystack : String) : Option (CapturedGroups haystack) :=
  regex.captures haystack |>.next? |>.map Prod.fst

/--
Captures all matches of a regex pattern in a string, including capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An array of `CapturedGroups`, each containing a match and its capture groups
-/
def captureAll (regex : Regex) (haystack : String) : Array (CapturedGroups haystack) :=
  go (regex.captures haystack) #[]
where
  go (m : Captures haystack) (accum : Array (CapturedGroups haystack)) : Array (CapturedGroups haystack) :=
    match _h : m.next? with
    | some (groups, m') => go m' (accum.push groups)
    | none => accum
  termination_by m

/--
Extracts the first regex match in a string.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: An optional string if a the match is found, or `none` otherwise
-/
def extract (regex : Regex) (haystack : String) : Option String :=
  regex.find haystack |>.map Slice.copy

/--
Extracts all regex matches in a string.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: an array containing all regex matches occuring in a string
-/
def extractAll (regex : Regex) (haystack : String) : Array String :=
  regex.findAll haystack |>.map Slice.copy

/--
Tests if a regex matches a string.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: `true` if the `Regex` matches, `false` otherwise
-/
def test (regex : Regex) (haystack : String) : Bool :=
  regex.find haystack |>.isSome

/--
Counts the number of regex matches in a string.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: the number of regex matches in a string
-/
def count (regex : Regex) (haystack : String) : Nat :=
  regex.findAll haystack |>.size

/--
Splits a string using regex matches as breakpoints.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: an array containing the substrings in between the regex matches
-/
def split (regex : Regex) (haystack : String) : Array Slice :=
  go (regex.matches haystack) #[] haystack.startValidPos
where
  go (m : Matches haystack) (accum : Array Slice) (endPos : ValidPos haystack) : Array Slice :=
    match h : m.next? with
    | some (s, m') =>
      have eq : s.str = haystack := Matches.str_eq_of_next?_some h
      let startPos := s.startInclusive.cast eq
      if le : endPos ≤ startPos then
        go m' (accum.push ⟨haystack, endPos, startPos, le⟩) (s.endExclusive.cast eq)
      else
        -- This should never happen
        go m' accum (s.endExclusive.cast eq)
    | none =>
      accum.push (haystack.replaceStart endPos)
  termination_by m

end Regex
