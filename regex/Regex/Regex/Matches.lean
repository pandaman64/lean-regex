import Regex.Regex.Basic
import Regex.Data.String

set_option autoImplicit false

open String (Pos.Raw ValidPos ValidPosPlusOne Slice)

namespace Regex

/--
A structure that enables iterating through all matches of a regex pattern in a string.

Provides a stateful iterator for finding all regex matches in a haystack string.
-/
structure Matches (haystack : String) where
  regex : Regex
  currentPos : ValidPosPlusOne haystack
deriving Repr

namespace Matches

variable {haystack : String}

/--
Gets the next match in the input string.

* `self`: The matches iterator
* Returns: An optional pair containing the matched slice and an updated iterator,
          or `none` if no more matches are found
-/
def next? (self : Matches haystack) : Option (Slice × Matches haystack) :=
  if h : self.currentPos.isValid then
    match h' : self.regex.searchNext (self.currentPos.asValidPos h) with
    | .none => .none
    | .some s =>
      have eq : s.str = haystack := searchNext_str_eq_some h'
      let nextPos := .validPos (eq ▸ s.endExclusive)
      let next :=
        if self.currentPos < nextPos then
          { self with currentPos := nextPos }
        else
          { self with currentPos := self.currentPos.next h }
      .some (s, next)
  else
    .none

theorem lt_next?_some' {s : Slice} {m m' : Matches haystack} (h : m.next? = some (s, m')) :
  m.currentPos < m'.currentPos := by
  unfold next? at h
  grind

def lt (m m' : Matches haystack) : Prop := m.currentPos < m'.currentPos

instance : LT (Matches haystack) := ⟨lt⟩

@[simp]
theorem lt_next?_some {s : Slice} {m m' : Matches haystack} (h : m.next? = some (s, m')) : m < m' :=
  lt_next?_some' h

theorem wellFounded_gt : WellFounded (fun (p : Matches haystack) q => q < p) :=
  InvImage.wf Matches.currentPos ValidPosPlusOne.wellFounded_gt

instance : WellFoundedRelation (Matches haystack) where
  rel p q := q < p
  wf := wellFounded_gt

macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : Regex.Matches _) < _
   simp [
    Matches.lt_next?_some (by assumption),
  ]) <;> done)

instance : Std.Stream (Matches haystack) Slice := ⟨Matches.next?⟩

end Matches

end Regex

/--
Creates a new `Matches` iterator for a regex pattern and input string.

* `regex`: The compiled regex pattern to use for matching
* `s`: The input string to search in
* Returns: A `Matches` iterator positioned at the start of the string
-/
def Regex.matches (regex : Regex) (s : String) : Matches s :=
  { regex := regex, currentPos := s.startValidPosPlusOne }
