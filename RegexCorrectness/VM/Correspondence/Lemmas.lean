import RegexCorrectness.VM.Correspondence.Basic

set_option autoImplicit false

open Regex.Data (Vec)
open String (Pos)

namespace Regex.NFA

theorem materializeRegexGroupsAux_snoc {accum groups tag first last} :
  materializeRegexGroupsAux accum (groups ++ [(tag, first, last)]) =
  fun tag' => if tag = tag' then .some (first, last) else materializeRegexGroupsAux accum groups tag' := by
  induction groups generalizing accum with
  | nil => simp [materializeRegexGroupsAux]
  | cons _ _ ih => simp [materializeRegexGroupsAux, ih]

theorem materializeRegexGroupsAux_swap {accum groups tag₁ first₁ last₁ tag₂ first₂ last₂} (h : tag₁ ≠ tag₂) :
  materializeRegexGroupsAux accum ((tag₁, first₁, last₁) :: (tag₂, first₂, last₂) :: groups) =
  materializeRegexGroupsAux accum ((tag₂, first₂, last₂) :: (tag₁, first₁, last₁) :: groups) := by
  simp [materializeRegexGroupsAux]
  congr! 1
  funext tag
  if h₁ : tag₁ = tag then
    have h₂ : tag₂ ≠ tag := (h₁ ▸ h).symm
    simp [h₁, h₂]
  else
    simp [h₁]

theorem materializeRegexGroupsAux_cons_of_not_in {accum groups tag first last}
  (h : ∀ tag' first' last', (tag', first', last') ∈ groups → tag ≠ tag') :
  materializeRegexGroupsAux accum ((tag, first, last) :: groups) =
  fun tag' => if tag = tag' then .some (first, last) else materializeRegexGroupsAux accum groups tag' := by
  induction groups generalizing accum with
  | nil => simp [materializeRegexGroupsAux]
  | cons head groups ih =>
    have ne : tag ≠ head.1 := by
      have := h head.1 head.2.1 head.2.2
      simp at this
      exact this
    have h' (tag' first' last') (mem : (tag', first', last') ∈ groups) : tag ≠ tag' := by
      have : (tag', first', last') ∈ head :: groups := by
        simp [mem]
      exact h tag' first' last' this
    rw [materializeRegexGroupsAux_swap ne, materializeRegexGroupsAux, ih h']
    rfl

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

end Regex.NFA
