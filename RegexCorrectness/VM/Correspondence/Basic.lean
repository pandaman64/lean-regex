import Regex.Data.Vec
import RegexCorrectness.NFA.Semantics.Equivalence

set_option autoImplicit false

open Regex.Data (Vec)
open String (Pos)

namespace Regex.NFA

def materializeRegexGroupsAux (accum : Nat → Option (Pos × Pos)) : List (Nat × Pos × Pos) → Nat → Option (Pos × Pos)
  | [] => accum
  | (tag, first, last) :: rest =>
    materializeRegexGroupsAux (fun tag' => if tag = tag' then .some (first, last) else accum tag') rest

/--
`denoteRegexGroups groups` constructs a mapping that associates each capture group's tag with the
start/end positions of the last appearance of the capture group in the input string.
-/
def materializeRegexGroups (groups : List (Nat × Pos × Pos)) : Nat → Option (Pos × Pos) :=
  materializeRegexGroupsAux (fun _ => .none) groups

def materializeUpdatesAux (n : Nat) (accum : Vec (Option Pos) n) : List (Nat × Pos) → Vec (Option Pos) n
  | [] => accum
  | (offset, pos) :: rest =>
    materializeUpdatesAux n (accum.setIfInBounds offset (some pos)) rest

/--
`materializeUpdates n updates` constructs a buffer of size `n` which interprets the updates list
as the writes to the buffer. When the same offset appears multiple times in the list, the last
one wins.
-/
def materializeUpdates (n : Nat) (updates : List (Nat × Pos)) : Vec (Option Pos) n :=
  materializeUpdatesAux n (Vec.ofFn fun _ => .none) updates

def EquivMaterializedUpdate {n} (groups : Nat → Option (Pos × Pos)) (updates : Vec (Option Pos) n) : Prop :=
  ∀ tag first last,
    ((h₁ : 2 * tag < n) → (groups tag = .some (first, last) ↔ updates[2 * tag] = .some first)) ∧
    ((h₂ : 2 * tag + 1 < n) → (groups tag = .some (first, last) ↔ updates[2 * tag + 1] = .some last))

end Regex.NFA
