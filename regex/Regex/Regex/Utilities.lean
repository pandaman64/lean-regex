import Regex.Regex.Elab
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

/--
Tests if a regex matches a string.

* `self`: The regex to match against
* `input`: The input string
* Returns: `true` if the `Regex` matches, `false` otherwise
-/
def test (self : Regex) (input : String) : Bool :=
  self.find input |>.isSome

#eval do
  let regex := re! r"\d{4}-\d{2}-\d{2}"
  let hasMatch := regex.test
    --"No match"
    "2025-05-24"
  IO.print hasMatch

/--
Splits a string using regex matches as breakpoints.

* `self`: The regex to match against
* `input`: The input string
* Returns: an array containing the substrings in between the regex matches
-/
def split (self : Regex) (input : String) : Array String :=
  -- TODO what is the intended behavior when matches overlap?
  let paddedMatches :=
    self.findAll input
      |>.insertIdx 0 ⟨input, 0, 0⟩
      |>.push ⟨input, input.endPos, input.endPos⟩
  let toSubstringInbetween : (Substring × Substring) → Substring :=
    fun (prev,next) => ⟨input,prev.stopPos,next.startPos⟩
  paddedMatches.zip (paddedMatches.drop 1)
    |>.map toSubstringInbetween
    |>.map Substring.toString
    |>.filter (not ∘ String.isEmpty)

#eval do
  let regex := re! r" "
  let split := regex.split "    This is a sentence.    "
  IO.print split

/--
Counts the number of regex matches in a string.

* `self`: The regex to match against
* `input`: The input string
* Returns: the number of regex matches in a string
-/
def count (self : Regex) (input : String) : Nat :=
  self.findAll input |>.size

#eval do
  let regex := re! r"\d{4}-\d{2}-\d{2}"
  let numberOfMatches := regex.count
    --"No match"
    "2025-05-24"
  IO.print numberOfMatches

#eval do
  let regex := re! r"\s+"
  let numberOfMatches := regex.count "         "
  IO.print numberOfMatches

/--
Extracts all regex matches in a string.

* `self`: The regex to match against
* `input`: The input string
* Returns: an array containing all regex matches occuring in a string
-/
def extractAll (self : Regex) (input : String) : Array String :=
  self.findAll input |>.map Substring.toString

#eval do
  let regex := re! r"\d{2}"
  let allMatches := regex.extractAll
    "1234"
  IO.print allMatches

end Regex
