import Regex.Regex.Iterators

open String (Pos)

namespace Regex

/--
Finds the first match of a regex pattern in a string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An optional substring representing the match, or `none` if no match is found
-/
def find (regex : Regex) (haystack : String) : Option Substring :=
  match regex.matches haystack |>.step with
  | .yield _ s _ => .some s
  | .skip _ _ => .none
  | .done _ => .none

/--
Finds all matches of a regex pattern in a string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An array of all matched substrings
-/
def findAll (regex : Regex) (haystack : String) : Array Substring :=
  regex.matches haystack |>.toArray

/--
Transforms the first match of a regex pattern using its capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `transformer`: The rule yielding the string to replace the match with
* Returns: The modified string, or the original string if no match is found
-/
def transform (regex : Regex) (haystack : String) (transformer : CapturedGroups → String) : String :=
  match regex.captures haystack |>.step with
  | .yield _ groups _ =>
    -- TODO: prove again that the first group is always present
    let s := groups.get 0 |>.get!
    haystack.extract 0 s.startPos ++ transformer groups ++ haystack.extract s.stopPos haystack.endPos
  | .skip _ _ => haystack
  | .done _ => haystack

/--
Transforms all matches of a regex pattern using its capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `transformer`: The rule yielding the string to replace the match with
* Returns: The modified string, or the original string if no matches are found
-/
def transformAll (regex : Regex) (haystack : String) (transformer : CapturedGroups → String) : String := Id.run do
  let mut accum := ""
  let mut lastPos : Pos := 0
  for groups in regex.captures haystack do
    -- TODO: prove again that the first group is always present
    let s := groups.get 0 |>.get!
    accum := accum ++ haystack.extract lastPos s.startPos ++ transformer groups
    lastPos := s.stopPos
  accum ++ haystack.extract lastPos haystack.endPos

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
+  transformAll regex haystack (fun _ => replacement)

/--
Captures the first match of a regex pattern in a string, including capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An optional `CapturedGroups` containing the match and its capture groups,
          or `none` if no match is found
-/
def capture (regex : Regex) (haystack : String) : Option CapturedGroups :=
  match regex.captures haystack |>.step with
  | .yield _ groups _ => .some groups
  | .skip _ _ => .none
  | .done _ => .none

/--
Captures all matches of a regex pattern in a string, including capture groups.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* Returns: An array of `CapturedGroups`, each containing a match and its capture groups
-/
def captureAll (regex : Regex) (haystack : String) : Array CapturedGroups :=
  regex.captures haystack |>.toArray

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
def split (regex : Regex) (haystack : String) : Array Substring := Id.run do
  let mut accum := #[]
  let mut lastPos : Pos := 0
  for groups in regex.captures haystack do
    let s := groups.get 0 |>.get!
    accum := accum.push ⟨haystack, lastPos, s.startPos⟩
    lastPos := s.stopPos
  accum.push ⟨haystack, lastPos, haystack.endPos⟩

end Regex
