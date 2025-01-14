import RegexCorrectness.Data.Expr.Semantics.CaptureGroups
import RegexCorrectness.NFA.Semantics.Equivalence

set_option autoImplicit false

open Regex.Data (CaptureGroups)
open String (Pos)

namespace Regex.NFA

/--
`materializeRegexGroups groups` constructs a mapping that associates each capture group's tag
with the start/end positions of the last appearance of the capture group in the input string.
-/
def materializeRegexGroups : CaptureGroups → Nat → Option (Pos × Pos)
  | .empty, _ => .none
  | .group tag first last groups, tag' =>
    if tag = tag' then
      .some (first, last)
    else
      materializeRegexGroups groups tag'
  | .concat g₁ g₂, tag =>
    -- The later one will be preferred
    materializeRegexGroups g₂ tag <|> materializeRegexGroups g₁ tag

def materializeUpdatesAux (n : Nat) (accum : Vector (Option Pos) n) : List (Nat × Pos) → Vector (Option Pos) n
  | [] => accum
  | (offset, pos) :: rest =>
    materializeUpdatesAux n (accum.setIfInBounds offset (some pos)) rest

/--
`materializeUpdates n updates` constructs a buffer of size `n` which interprets the updates list
as the writes to the buffer. When the same offset appears multiple times in the list, the last
one wins.
-/
def materializeUpdates (n : Nat) (updates : List (Nat × Pos)) : Vector (Option Pos) n :=
  materializeUpdatesAux n (Vector.mkVector n .none) updates

def EquivMaterializedUpdate {n} (groups : Nat → Option (Pos × Pos)) (updates : Vector (Option Pos) n) : Prop :=
  ∀ tag,
    ((h₁ : 2 * tag < n) → ((groups tag).map (·.1) = updates[2 * tag])) ∧
    ((h₂ : 2 * tag + 1 < n) → ((groups tag).map (·.2) = updates[2 * tag + 1]))

end Regex.NFA
