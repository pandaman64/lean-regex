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
Replaces the first match of a regex pattern with a replacement string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `replacement`: The string to replace the match with
* Returns: The modified string, or the original string if no match is found
-/
def replace (regex : Regex) (haystack : String) (replacement : String) : String :=
  match regex.find haystack with
  | some s =>
    haystack.extract 0 s.startPos ++ replacement ++ haystack.extract s.stopPos haystack.endPos
  | none => haystack

/--
Replaces all matches of a regex pattern with a replacement string.

* `regex`: The compiled regex pattern to use for matching
* `haystack`: The input string to search in
* `replacement`: The string to replace the matches with
* Returns: The modified string, or the original string if no matches are found
-/
def replaceAll (regex : Regex) (haystack : String) (replacement : String) : String :=
  go (regex.matches haystack) "" 0
where
  go (m : Matches) (accum : String) (endPos : Pos) : String :=
    match _h : m.next? with
    | some (s, m') =>
      go m' (accum ++ haystack.extract endPos s.startPos ++ replacement) s.stopPos
    | none =>
      accum ++ haystack.extract endPos haystack.endPos
  termination_by m.remaining

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

end Regex
