import RegexCorrectness.VM.Correspondence.Materialize.Basic

set_option autoImplicit false

open Regex.Data (Vec)
open String (Pos)

namespace Regex.NFA

@[simp]
theorem materializeRegexGroups_empty : materializeRegexGroups .empty = fun _ => .none := rfl

@[simp]
theorem materializeRegexGroups_group {tag first last groups} :
  materializeRegexGroups (.group tag first last groups) =
  fun tag' => if tag = tag' then .some (first, last) else materializeRegexGroups groups tag' := rfl

@[simp]
theorem materializeRegexGroups_concat {g₁ g₂} :
  materializeRegexGroups (.concat g₁ g₂) =
  fun tag => materializeRegexGroups g₂ tag <|> materializeRegexGroups g₁ tag := rfl

@[simp]
theorem materializeUpdatesAux_snoc {n accum updates offset pos} :
  materializeUpdatesAux n accum (updates ++ [(offset, pos)]) =
  (materializeUpdatesAux n accum updates).setIfInBounds offset (some pos) := by
  induction updates generalizing accum with
  | nil => simp [materializeUpdatesAux]
  | cons _ _ ih => simp [materializeUpdatesAux, ih]

theorem materializeUpdatesAux_swap {n accum updates offset₁ pos₁ offset₂ pos₂} (ne : offset₁ ≠ offset₂) :
  materializeUpdatesAux n accum ((offset₁, pos₁) :: (offset₂, pos₂) :: updates) =
  materializeUpdatesAux n accum ((offset₂, pos₂) :: (offset₁, pos₁) :: updates) := by
  simp [materializeUpdatesAux]
  congr! 1
  simp [Vec.ext_iff]
  intro i h
  if h₁ : offset₁ = i then
    have h₂ : offset₂ ≠ i := (h₁ ▸ ne).symm
    simp [h₁, h₂]
  else
    if h₂ : offset₂ = i then
      simp [h₁, h₂]
    else
      simp [h₁, h₂]

theorem materializeUpdatesAux_cons_of_not_in {n accum updates offset pos}
  (h : ∀ offset' pos', (offset', pos') ∈ updates → offset ≠ offset') :
  materializeUpdatesAux n accum ((offset, pos) :: updates) =
  (materializeUpdatesAux n accum updates).setIfInBounds offset (some pos) := by
  induction updates generalizing accum with
  | nil => simp [materializeUpdatesAux]
  | cons head updates ih =>
    have ne : offset ≠ head.1 := by
      have := h head.1 head.2
      simp at this
      exact this
    have h' (offset' pos') (mem : (offset', pos') ∈ updates) : offset ≠ offset' := by
      have : (offset', pos') ∈ head :: updates := by
        simp [mem]
      exact h offset' pos' this
    rw [materializeUpdatesAux_swap ne, materializeUpdatesAux, ih h']
    rfl

@[simp]
theorem materializeUpdatesAux_nil {n accum} : materializeUpdatesAux n accum [] = accum := rfl

theorem materializeUpdatesAux_append {n accum updates₁ updates₂} :
  materializeUpdatesAux n accum (updates₁ ++ updates₂) = materializeUpdatesAux n (materializeUpdatesAux n accum updates₁) updates₂ := by
  induction updates₁ generalizing accum with
  | nil => simp
  | cons head tail ih => simp [materializeUpdatesAux, ih]

theorem materializeUpdatesAux_getElem {n accum updates} {offset : Nat} (h : offset < n) :
  (materializeUpdatesAux n accum updates)[offset] =
  ((materializeUpdatesAux n (Vec.ofFn fun _ => .none) updates)[offset] <|> accum[offset]) := by
  induction updates generalizing accum with
  | nil => simp
  | cons head updates ih =>
    simp [materializeUpdatesAux]
    conv =>
      lhs
      rw [ih]
    conv =>
      rhs
      rw [ih]
    cases (materializeUpdatesAux n (Vec.ofFn fun x => none) updates)[offset] with
    | some _ => simp
    | none =>
      simp
      if h' : head.1 = offset then
        simp [h']
      else
        simp [h']

@[simp]
theorem materializeUpdates_empty {n} : materializeUpdates n [] = Vec.ofFn (fun _ => .none) := rfl

@[simp]
theorem materializeUpdates_snoc {n updates offset pos} :
  materializeUpdates n (updates ++ [(offset, pos)]) =
  (materializeUpdates n updates).setIfInBounds offset (some pos) := by
  simp [materializeUpdates]

theorem materializeUpdates_append_getElem {n updates₁ updates₂} {offset : Nat} (h : offset < n) :
  (materializeUpdates n (updates₁ ++ updates₂))[offset] =
  ((materializeUpdates n updates₂)[offset] <|> (materializeUpdates n updates₁)[offset]) := by
  conv =>
    lhs
    simp [materializeUpdates, materializeUpdatesAux_append]
    rw [materializeUpdatesAux_getElem h]
  rfl

end Regex.NFA
