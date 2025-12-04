import RegexCorrectness.Data.Expr.Semantics.CaptureGroups

set_option autoImplicit false

open Regex.Data (CaptureGroups)
open String (ValidPos)

namespace Regex.Strategy

variable {s : String}

/--
`materializeRegexGroups groups` constructs a mapping that associates each capture group's tag
with the start/end positions of the last appearance of the capture group in the input string.
-/
def materializeRegexGroups : CaptureGroups s → Nat → Option (ValidPos s × ValidPos s)
  | .empty, _ => .none
  | .group tag first last groups, tag' =>
    if tag = tag' then
      .some (first, last)
    else
      materializeRegexGroups groups tag'
  | .concat g₁ g₂, tag =>
    -- The later one will be preferred
    materializeRegexGroups g₂ tag <|> materializeRegexGroups g₁ tag

def materializeUpdatesAux (n : Nat) (accum : Vector (Option (ValidPos s)) n) : List (Nat × ValidPos s) → Vector (Option (ValidPos s)) n
  | [] => accum
  | (offset, pos) :: rest =>
    materializeUpdatesAux n (accum.setIfInBounds offset (some pos)) rest

/--
`materializeUpdates n updates` constructs a buffer of size `n` which interprets the updates list
as the writes to the buffer. When the same offset appears multiple times in the list, the last
one wins.
-/
def materializeUpdates (n : Nat) (updates : List (Nat × ValidPos s)) : Vector (Option (ValidPos s)) n :=
  materializeUpdatesAux n (Vector.replicate n .none) updates

def EquivMaterializedUpdate {n} (groups : Nat → Option (ValidPos s × ValidPos s)) (updates : Vector (Option (ValidPos s)) n) : Prop :=
  ∀ tag,
    ((h₁ : 2 * tag < n) → ((groups tag).map (·.1) = updates[2 * tag])) ∧
    ((h₂ : 2 * tag + 1 < n) → ((groups tag).map (·.2) = updates[2 * tag + 1]))

theorem EquivMaterializedUpdate.eq {n} {groups : Nat → Option (ValidPos s × ValidPos s)} {updates : Vector (Option (ValidPos s)) n}
  (eqv : EquivMaterializedUpdate groups updates) (tag : Nat) (lt : 2 * tag + 1 < n) (p₁ p₂ : ValidPos s) :
  groups tag = .some (p₁, p₂) ↔ updates[2 * tag] = .some p₁ ∧ updates[2 * tag + 1] = .some p₂ := by
  have eq₁ := (eqv tag).1 (by grind)
  have eq₂ := (eqv tag).2 lt
  match h : groups tag with
  | .some (p₁', p₂') => grind
  | .none => grind

end Regex.Strategy
