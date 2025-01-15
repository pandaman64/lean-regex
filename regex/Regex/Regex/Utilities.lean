import Regex.Regex.Matches
import Regex.Regex.Captures

open String (Pos)

namespace Regex

def find (regex : Regex) (haystack : String) : Option (Pos × Pos) :=
  regex.matches haystack |>.next? |>.map Prod.fst

def findAll (regex : Regex) (haystack : String) : Array (Pos × Pos) :=
  go (regex.matches haystack) #[]
where
  go (m : Matches) (accum : Array (Pos × Pos)) : Array (Pos × Pos) :=
    match _h : m.next? with
    | some (pos, m') => go m' (accum.push pos)
    | none => accum
  termination_by m.remaining

def replace (regex : Regex) (haystack : String) (replacement : String) : String :=
  match regex.find haystack with
  | some (startPos, endPos) =>
    haystack.extract 0 startPos ++ replacement ++ haystack.extract endPos haystack.endPos
  | none => haystack

def replaceAll (regex : Regex) (haystack : String) (replacement : String) : String :=
  go (regex.matches haystack) "" 0
where
  go (m : Matches) (accum : String) (endPos : Pos) : String :=
    match _h : m.next? with
    | some ((startPos', endPos'), m') =>
      go m' (accum ++ haystack.extract endPos startPos' ++ replacement) endPos'
    | none =>
      accum ++ haystack.extract endPos haystack.endPos
  termination_by m.remaining

def capture (regex : Regex) (haystack : String) : Option CapturedGroups :=
  regex.captures haystack |>.next? |>.map Prod.fst

def captureAll (regex : Regex) (haystack : String) : Array CapturedGroups :=
  go (regex.captures haystack) #[]
where
  go (m : Captures) (accum : Array CapturedGroups) : Array CapturedGroups :=
    match _h : m.next? with
    | some (groups, m') => go m' (accum.push groups)
    | none => accum
  termination_by m.remaining

end Regex
