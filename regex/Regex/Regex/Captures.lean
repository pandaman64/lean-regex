import Regex.Regex.Basic

set_option autoImplicit false

open String (Pos ValidPosPlusOne Slice)

namespace Regex

variable {haystack : String}

/--
A structure representing the capture groups from a regex match.

Contains the original string (haystack) and a buffer of positions marking
the start and end of each capture group.
-/
structure CapturedGroups (haystack : String) where
  buffer : Array (ValidPosPlusOne haystack)
deriving Repr, DecidableEq, Inhabited

/--
Gets a specific capture group as a substring.

* `self`: The captured groups
* `index`: The index of the capture group to retrieve (0 for the entire match)
* Returns: An optional substring representing the capture group, or `none` if the group didn't participate in the match
-/
def CapturedGroups.get (self : CapturedGroups haystack) (index : Nat) : Option Slice := do
  let start ← self.buffer[2 * index]?
  let stop ← self.buffer[2 * index + 1]?
  if h : stop.isValid && start ≤ stop then
    have isStopPosValid : stop.isValid := by grind
    have isStartPosValid : start.isValid := ValidPosPlusOne.isValid_of_isValid_of_le isStopPosValid (by grind)
    return ⟨haystack, start.asPos isStartPosValid, stop.asPos isStopPosValid, ValidPosPlusOne.le_iff.mp (by grind)⟩
  else
    throw ()

theorem CapturedGroups.get_str_eq_some {self : CapturedGroups haystack} {index : Nat} {s : Slice}
  (h : self.get index = some s) :
  s.str = haystack := by
  simp [get, Option.bind_eq_some_iff] at h
  grind

/--
Converts all capture groups to an array of optional substrings.

* `self`: The captured groups
* Returns: An array where each element is either a substring for a capture group
          or `none` if that group didn't participate in the match
-/
def CapturedGroups.toArray (self : CapturedGroups haystack) : Array (Option Slice) :=
  go 0 #[]
where
  go (i : Nat) (accum : Array (Option Slice)) : Array (Option Slice) :=
    if 2 * i < self.buffer.size then
      go (i + 1) (accum.push (self.get i))
    else
      accum

/--
A structure that enables iterating through all capture groups of regex matches in a string.

Provides a stateful iterator for finding all regex matches and their capture groups
in a haystack string.
-/
structure Captures (haystack : String) where
  regex : Regex
  currentPos : ValidPosPlusOne haystack
deriving Repr

namespace Captures

/--
Gets the next match and its capture groups.

* `self`: The captures iterator
* Returns: An optional pair containing the captured groups and an updated iterator,
          or `none` if no more matches are found
-/
def next? (self : Captures haystack) : Option (CapturedGroups haystack × Captures haystack) :=
  if h : self.currentPos.isValid then
    match self.regex.captureNextBuf (self.regex.maxTag + 1) (self.currentPos.asPos h) with
    | .none => .none
    | .some buffer =>
      let groups : CapturedGroups haystack := ⟨buffer.toArray⟩
      match h' : groups.get 0 with
      | .none => .none
      | .some s =>
        have eq : s.str = haystack := CapturedGroups.get_str_eq_some h'
        let nextPos := .validPos (eq ▸ s.endExclusive)
        let next :=
          if self.currentPos < nextPos then
            { self with currentPos := nextPos }
          else
            { self with currentPos := self.currentPos.next h }
        pure (groups, next)
  else
    throw ()

theorem zeroth_group_some_of_next?_some {self next : Captures haystack} {groups : CapturedGroups haystack}
  (h : self.next? = (groups, next)) :
  groups.get 0 |>.isSome := by
  unfold next? at h
  split at h <;> try contradiction
  split at h <;> simp at h
  split at h <;> simp at h
  next eq => simp [←h, eq]

theorem lt_next?_some' {groups : CapturedGroups haystack} {c c' : Captures haystack} (h : c.next? = some (groups, c')) :
  c.currentPos < c'.currentPos := by
  unfold next? at h
  grind

def lt (c c' : Captures haystack) : Prop := c.currentPos < c'.currentPos

instance : LT (Captures haystack) := ⟨lt⟩

@[simp]
theorem lt_next?_some {groups : CapturedGroups haystack} {c c' : Captures haystack} (h : c.next? = some (groups, c')) : c < c' :=
  lt_next?_some' h

theorem wellFounded_gt : WellFounded (fun (p : Captures haystack) q => q < p) :=
  InvImage.wf Captures.currentPos ValidPosPlusOne.wellFounded_gt

instance : WellFoundedRelation (Captures haystack) where
  rel p q := q < p
  wf := wellFounded_gt

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : Regex.Captures _) < _
   simp [
    Captures.lt_next?_some (by assumption),
  ]) <;> done)

instance : Std.Stream (Captures haystack) (CapturedGroups haystack) := ⟨Captures.next?⟩

end Captures

end Regex

/--
Creates a new `Captures` iterator for a regex pattern and input string.

* `regex`: The compiled regex pattern to use for matching
* `s`: The input string to search in
* Returns: A `Captures` iterator positioned at the start of the string
-/
def Regex.captures (regex : Regex) (s : String) : Captures s :=
  { regex := regex, currentPos := s.startValidPosPlusOne }
