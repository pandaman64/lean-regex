import RegexCorrectness.Data.Expr.Semantics.CaptureGroups

set_option autoImplicit false

open Regex.Data (CaptureGroups)
open String (Pos PosPlusOne)

namespace Regex.Strategy

variable {s : String}

/--
`materializeRegexGroups groups` constructs a mapping that associates each capture group's tag
with the start/end positions of the last appearance of the capture group in the input string.
-/
def materializeRegexGroups : CaptureGroups s → Nat → Option (Pos s × Pos s)
  | .empty, _ => .none
  | .group tag first last groups, tag' =>
    if tag = tag' then
      .some (first, last)
    else
      materializeRegexGroups groups tag'
  | .concat g₁ g₂, tag =>
    -- The later one will be preferred
    materializeRegexGroups g₂ tag <|> materializeRegexGroups g₁ tag

def materializeUpdatesAux (n : Nat) (accum : Vector (PosPlusOne s) n) : List (Nat × Pos s) → Vector (PosPlusOne s) n
  | [] => accum
  | (offset, pos) :: rest =>
    materializeUpdatesAux n (accum.setIfInBounds offset (.pos pos)) rest

/--
`materializeUpdates n updates` constructs a buffer of size `n` which interprets the updates list
as the writes to the buffer. When the same offset appears multiple times in the list, the last
one wins.
-/
def materializeUpdates (n : Nat) (updates : List (Nat × Pos s)) : Vector (PosPlusOne s) n :=
  materializeUpdatesAux n (Vector.replicate n (.sentinel s)) updates

def equivPos {s} (p : Option (Pos s)) (p' : PosPlusOne s) : Prop :=
  match p with
  | .some p => p' = .pos p
  | .none => p' = .sentinel s

@[simp, grind =]
theorem equivPos.some_iff {p : Pos s} {p' : PosPlusOne s} : equivPos (.some p) p' ↔ p' = .pos p := by
  grind [equivPos]

@[simp, grind =]
theorem equivPos.none_iff {p' : PosPlusOne s} : equivPos .none p' ↔ p' = .sentinel s := by
  grind [equivPos]

@[simp, grind =]
theorem equivPos.pos_iff {p p' : Pos s} : equivPos p (.pos p') ↔ p = p' := by
  grind [equivPos]

@[simp, grind =]
theorem equivPos.sentinel_iff {p} : equivPos p (.sentinel s) ↔ p = .none := by
  match p with
  | .some p => simpa using PosPlusOne.pos_ne_sentinel.symm
  | .none => simp

def EquivMaterializedUpdate {n} (groups : Nat → Option (Pos s × Pos s)) (updates : Vector (PosPlusOne s) n) : Prop :=
  ∀ tag,
    ((h₁ : 2 * tag < n) → (equivPos ((groups tag).map (·.1)) updates[2 * tag])) ∧
    ((h₂ : 2 * tag + 1 < n) → (equivPos ((groups tag).map (·.2)) updates[2 * tag + 1]))

theorem EquivMaterializedUpdate.eq {n} {groups : Nat → Option (Pos s × Pos s)} {updates : Vector (PosPlusOne s) n}
  (eqv : EquivMaterializedUpdate groups updates) (tag : Nat) (lt : 2 * tag + 1 < n) (p₁ p₂ : Pos s) :
  groups tag = .some (p₁, p₂) ↔ updates[2 * tag] = .pos p₁ ∧ updates[2 * tag + 1] = .pos p₂ := by
  have eq₁ := (eqv tag).1 (by grind)
  have eq₂ := (eqv tag).2 lt
  match h : groups tag with
  | .some (p₁', p₂') => grind
  | .none => grind

theorem EquivMaterializedUpdate.eq_none {n} {groups : Nat → Option (Pos s × Pos s)} {updates : Vector (PosPlusOne s) n}
  (eqv : EquivMaterializedUpdate groups updates) (tag : Nat) (lt : 2 * tag + 1 < n) :
  groups tag = .none ↔ updates[2 * tag] = .sentinel s ∧ updates[2 * tag + 1] = .sentinel s := by
  have eq₁ := (eqv tag).1 (by grind)
  have eq₂ := (eqv tag).2 lt
  match h : groups tag with
  | .some (p₁', p₂') => grind
  | .none => grind

end Regex.Strategy
