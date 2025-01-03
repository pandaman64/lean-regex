import RegexCorrectness.Data.Expr.Semantics

set_option autoImplicit false

open Regex.Data (CaptureGroups)

namespace Regex.NFA

inductive EquivUpdate : CaptureGroups → List (Nat × String.Pos) → Prop where
  | empty : EquivUpdate .empty []
  | group {groups updates tag first last} (eqv : EquivUpdate groups updates) :
    EquivUpdate (.group tag first last groups) ((2 * tag, first) :: updates ++ [(2 * tag + 1, last)])
  | concat {groups₁ groups₂ updates₁ updates₂} (eqv₁ : EquivUpdate groups₁ updates₁) (eqv₂ : EquivUpdate groups₂ updates₂) :
    EquivUpdate (.concat groups₁ groups₂) (updates₁ ++ updates₂)

theorem EquivUpdate.mem_groups_of_mem_updates {groups updates offset pos}
  (h : (offset, pos) ∈ updates) (eqv : EquivUpdate groups updates) :
  ∃ tag first last, (tag, first, last) ∈ groups ∧ (offset = 2 * tag ∨ offset = 2 * tag + 1) := by
  induction eqv with
  | empty => simp at h
  | @group groups updates tag first last eqv ih =>
    simp at h
    match h with
    | .inl eq => exact ⟨tag, first, last, by simp, by simp [eq]⟩
    | .inr (.inl mem) =>
      have ⟨tag, first, last, mem, eq⟩ := ih mem
      exact ⟨tag, first, last, by simp [mem], eq⟩
    | .inr (.inr eq) => exact ⟨tag, first, last, by simp, by simp [eq]⟩
  | @concat groups₁ groups₂ updates₁ updates₂ eqv₁ eqv₂ ih₁ ih₂ =>
    simp at h
    cases h with
    | inl mem =>
      have ⟨tag, first, last, mem, eq⟩ := ih₁ mem
      exact ⟨tag, first, last, by simp [mem], eq⟩
    | inr mem =>
      have ⟨tag, first, last, mem, eq⟩ := ih₂ mem
      exact ⟨tag, first, last, by simp [mem], eq⟩

end Regex.NFA
