import Regex.Data.Expr

set_option autoImplicit false

open String (Pos)

namespace Regex.Data

/--
Groups captured by a regex match.

- For `.group tag first last rest`, the group with tag `tag` starts at position `first` and ends at
  position `last`. It will overwrite the positions with the same tag in `rest`.
- `.concat g₁ g₂` joins the capture groups for concatenations by preferring the groups in `g₂` over `g₁`.
  (Last write wins.)
-/
inductive CaptureGroups : Type where
  | empty : CaptureGroups
  | group (tag : Nat) (first last : Pos) (rest : CaptureGroups) : CaptureGroups
  | concat (g₁ g₂ : CaptureGroups) : CaptureGroups

namespace CaptureGroups

def mem (groups : CaptureGroups) (group : Nat × Pos × Pos) : Prop :=
  match groups with
  | .empty => False
  | .group tag first last rest => (tag = group.1 ∧ first = group.2.1 ∧ last = group.2.2) ∨ rest.mem group
  | .concat g₁ g₂ => g₁.mem group ∨ g₂.mem group

instance : Membership (Nat × Pos × Pos) CaptureGroups where
  mem := CaptureGroups.mem

@[simp]
theorem mem_empty {group} : group ∈ CaptureGroups.empty ↔ False := by
  simp [Membership.mem, mem]

@[simp]
theorem mem_group {group tag first last rest} :
  group ∈ CaptureGroups.group tag first last rest ↔ (group = (tag, first, last) ∨ group ∈ rest) := by
  simp [Membership.mem, mem]
  apply Iff.intro
  . intro h
    cases h <;> simp [*]
  . intro h
    cases h <;> simp [*]

@[simp]
theorem mem_concat {group g₁ g₂} : group ∈ CaptureGroups.concat g₁ g₂ ↔ (group ∈ g₁ ∨ group ∈ g₂) := by
  simp [Membership.mem, mem]

end CaptureGroups

end Regex.Data
