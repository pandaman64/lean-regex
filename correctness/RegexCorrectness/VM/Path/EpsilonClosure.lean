import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open Regex.Data (Span)
open String (Pos)

-- Transition relations specialized for ε-closure traversal.
namespace Regex.NFA

def εStep' (nfa : NFA) (span : Span) (i j : Fin nfa.nodes.size) (update : Option (Nat × Pos)) : Prop :=
  nfa.Step 0 i span j span update

section

variable {nfa : NFA} {span i j update}

@[simp]
theorem εStep'.done (hn : nfa[i] = .done) :
  nfa.εStep' span i j update ↔ False := by
  apply Step.iff_done hn

@[simp]
theorem εStep'.fail (hn : nfa[i] = .fail) :
  nfa.εStep' span i j update ↔ False := by
  apply Step.iff_fail hn

@[simp]
theorem εStep'.epsilon {next} (hn : nfa[i] = .epsilon next) :
  nfa.εStep' span i j update ↔ j = next ∧ update = .none := by
  simp [εStep', Step.iff_epsilon hn]
  omega

@[simp]
theorem εStep'.anchor {anchor next} (hn : nfa[i] = .anchor anchor next) :
  nfa.εStep' span i j update ↔ j = next ∧ update = .none ∧ anchor.test span.iterator := by
  simp [εStep', Step.iff_anchor hn]
  omega

@[simp]
theorem εStep'.split {next₁ next₂} (hn : nfa[i] = .split next₁ next₂) :
  nfa.εStep' span i j update ↔ (j = next₁ ∨ j = next₂) ∧ update = .none := by
  simp [εStep', Step.iff_split hn]
  omega

@[simp]
theorem εStep'.save {offset next} (hn : nfa[i] = .save offset next) :
  nfa.εStep' span i j update ↔ j = next ∧ update = .some (offset, span.curr) := by
  simp [εStep', Step.iff_save hn]
  omega

@[simp]
theorem εStep'.char {c next} (hn : nfa[i] = .char c next) :
  nfa.εStep' span i j update ↔ False := by
  rw [εStep']
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . exact fun f => False.elim f

@[simp]
theorem εStep'.sparse {cs next} (hn : nfa[i] = .sparse cs next) :
  nfa.εStep' span i j update ↔ False := by
  rw [εStep']
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . exact fun f => False.elim f

end

inductive εClosure' (nfa : NFA) (span : Span) : Fin nfa.nodes.size → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | base {i} : εClosure' nfa span i i []
  | step {i j k update₁ update₂} (step : nfa.εStep' span i j update₁) (rest : εClosure' nfa span j k update₂) :
    εClosure' nfa span i k (update₁ ::ₒ update₂)

theorem εClosure'.single {nfa : NFA} {span i j update} (step : nfa.εStep' span i j update) :
  εClosure' nfa span i j (List.ofOption update) := by
  have := εClosure'.step step εClosure'.base
  simp at this
  exact this

theorem εClosure'.trans {nfa : NFA} {span i j k update₁ update₂}
  (cls₁ : εClosure' nfa span i j update₁) (cls₂ : εClosure' nfa span j k update₂) :
  εClosure' nfa span i k (update₁ ++ update₂) := by
  induction cls₁ with
  | base => exact cls₂
  | step step rest ih =>
    simp
    exact .step step (ih cls₂)

theorem εClosure'.snoc {nfa : NFA} {span i j k update₁ update₂}
  (cls : εClosure' nfa span i j update₁) (step : nfa.εStep' span j k update₂) :
  εClosure' nfa span i k (update₁ ++ List.ofOption update₂) :=
  cls.trans (εClosure'.single step)

theorem εClosure'_of_path {nfa : NFA} {i j span span' updates} (wf : nfa.WellFormed) (hspan : span = span')
  (path : nfa.Path 0 i span j span' updates) :
  nfa.εClosure' span ⟨i, path.lt⟩ ⟨j, path.lt_right wf⟩ updates := by
  induction path with
  | last step =>
    subst hspan
    exact εClosure'.single step
  | @more i span j span' k span'' update₁ update₂ step rest ih =>
    match step.span_eq_or_next with
    | .inl hspan' =>
      subst hspan hspan'
      simp at ih
      exact .step (by simp [εStep', step]) ih
    | .inr ⟨c, r, _, hspan'⟩ =>
      subst hspan hspan'
      have := rest.le_length
      simp at this
      omega

theorem εClosure'_iff_path (nfa : NFA) (wf : nfa.WellFormed) (i j : Fin nfa.nodes.size) (span : Span) (updates : List (Nat × Pos)) :
  nfa.εClosure' span i j updates ↔ (i = j ∧ updates = []) ∨ nfa.Path 0 i span j span updates := by
  apply Iff.intro
  . intro cls
    induction cls with
    | base => simp
    | step step rest ih =>
      match ih with
      | .inl ⟨eqj, equ⟩ =>
        simp [equ]
        exact .inr (.last (eqj ▸ step))
      | .inr path => exact .inr (.more step path)
  . intro path
    cases path with
    | inl eq => simp [eq, εClosure'.base]
    | inr path => exact εClosure'_of_path wf rfl path

end Regex.NFA
