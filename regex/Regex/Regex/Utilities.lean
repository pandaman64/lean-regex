import Regex.Regex.Matches
import Regex.Regex.Captures

open String (Pos)

namespace Regex

/--
Finds the first match of a regex pattern in a string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An optional substring representing the match, or `none` if no match is found
-/
def find (regex : Regex) (haystack : String) : Option Substring :=
  regex.matches haystack |>.next? |>.map Prod.fst

/--
Finds all matches of a regex pattern in a string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An array of all matched substrings
-/
def findAll (regex : Regex) (haystack : String) : Array Substring :=
  go (regex.matches haystack) #[]
where
  go (m : Matches) (accum : Array Substring) : Array Substring :=
    match _h : m.next? with
    | some (pos, m') => go m' (accum.push pos)
    | none => accum
  termination_by m.remaining

/--
Transforms the first match of a regex pattern using its capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `transformer`: The rule yielding the string to replace the match with
* Returns: The modified string, or the original string if no match is found
-/
def transform (regex : Regex) (haystack : String) (transformer : CapturedGroups → String) : String :=
    match h : (regex.captures haystack).next? with
  | some (g,_) =>
    let s := g.get 0 |>.get (Captures.zeroth_group_some_of_next?_some h)
    haystack.extract 0 s.startPos ++ transformer g ++ haystack.extract s.stopPos haystack.endPos
  | none => haystack

/--
Transforms all matches of a regex pattern using its capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `transformer`: The rule yielding the string to replace the match with
* Returns: The modified string, or the original string if no matches are found
-/
def transformAll (regex : Regex) (haystack : String) (transformer : CapturedGroups → String) : String :=
  go (regex.captures haystack) "" 0
where
  go (c : Captures) (accum : String) (endPos : Pos) : String :=
    match h : c.next? with
    | some (g, c') =>
      let s := g.get 0 |>.get (Captures.zeroth_group_some_of_next?_some h)
      go c' (accum ++ haystack.extract endPos s.startPos ++ transformer g) s.stopPos
    | none =>
      accum ++ haystack.extract endPos haystack.endPos
  termination_by c.remaining

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
def capture (regex : Regex) (haystack : String) : Option CapturedGroups :=
  regex.captures haystack |>.next? |>.map Prod.fst

/--
Captures all matches of a regex pattern in a string, including capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An array of `CapturedGroups`, each containing a match and its capture groups
-/
def captureAll (regex : Regex) (haystack : String) : Array CapturedGroups :=
  go (regex.captures haystack) #[]
where
  go (m : Captures) (accum : Array CapturedGroups) : Array CapturedGroups :=
    match _h : m.next? with
    | some (groups, m') => go m' (accum.push groups)
    | none => accum
  termination_by m.remaining

/--
Extracts the first regex match in a string.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: An optional string if a the match is found, or `none` otherwise
-/
def extract (regex : Regex) (haystack : String) : Option String :=
  regex.find haystack |>.map Substring.toString

/--
Extracts all regex matches in a string.

* `regex`: The regex to match against
* `haystack`: The input string to search in
* Returns: an array containing all regex matches occuring in a string
-/
def extractAll (regex : Regex) (haystack : String) : Array String :=
  regex.findAll haystack |>.map Substring.toString

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
def split (regex : Regex) (haystack : String) : Array Substring :=
  go (regex.matches haystack) #[] 0
where
  go (m : Matches) (accum : Array Substring) (endPos : Pos) : Array Substring :=
    match _h : m.next? with
    | some (s, m') =>
      go m' (accum.push ⟨haystack, endPos, s.startPos⟩) s.stopPos
    | none =>
      accum.push ⟨haystack, endPos, haystack.endPos⟩
  termination_by m.remaining

end Regex
