import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (ValidPos)
open String.Pos (Raw)

-- Transition relations specialized for ε-closure traversal.
namespace Regex.NFA

def εStep' {s : String} (nfa : NFA) (pos : ValidPos s) (i j : Fin nfa.nodes.size) (update : Option (Nat × ValidPos s)) : Prop :=
  nfa.Step 0 i pos j pos update

section

variable {s : String} {nfa : NFA} {pos : ValidPos s} {i j update}

@[grind =]
theorem εStep'.done (hn : nfa[i] = .done) :
  nfa.εStep' pos i j update ↔ False := by
  apply Step.iff_done hn

@[grind =]
theorem εStep'.fail (hn : nfa[i] = .fail) :
  nfa.εStep' pos i j update ↔ False := by
  apply Step.iff_fail hn

@[grind =>]
theorem εStep'.epsilon {next : Nat} (hn : nfa[i] = .epsilon next) :
  nfa.εStep' pos i j update ↔ j = next ∧ update = .none := by
  simp [εStep', Step.iff_epsilon hn]

@[grind =>]
theorem εStep'.anchor {anchor} {next : Nat} (hn : nfa[i] = .anchor anchor next) :
  nfa.εStep' pos i j update ↔ j = next ∧ update = .none ∧ anchor.test pos := by
  simp [εStep', Step.iff_anchor hn]

@[grind =>]
theorem εStep'.split {next₁ next₂ : Nat} (hn : nfa[i] = .split next₁ next₂) :
  nfa.εStep' pos i j update ↔ (j = next₁ ∨ j = next₂) ∧ update = .none := by
  simp [εStep', Step.iff_split hn]

@[grind =>]
theorem εStep'.save {offset} {next : Nat} (hn : nfa[i] = .save offset next) :
  nfa.εStep' pos i j update ↔ j = next ∧ update = .some (offset, pos) := by
  simp [εStep', Step.iff_save hn]

@[grind =>]
theorem εStep'.char {c} {next : Nat} (hn : nfa[i] = .char c next) :
  nfa.εStep' pos i j update ↔ False := by
  simp [εStep', Step.iff_char hn]

@[grind =>]
theorem εStep'.sparse {cs} {next : Nat} (hn : nfa[i] = .sparse cs next) :
  nfa.εStep' pos i j update ↔ False := by
  simp [εStep', Step.iff_sparse hn]

end

inductive εClosure' {s : String} (nfa : NFA) (pos : ValidPos s) : Fin nfa.nodes.size → Fin nfa.nodes.size → List (Nat × ValidPos s) → Prop where
  | base {i} : εClosure' nfa pos i i []
  | step {i j k update₁ update₂} (step : nfa.εStep' pos i j update₁) (rest : εClosure' nfa pos j k update₂) :
    εClosure' nfa pos i k (update₁ ::ₒ update₂)

theorem εClosure'.single {nfa : NFA} {s : String} {pos : ValidPos s} {i j update} (step : nfa.εStep' pos i j update) :
  εClosure' nfa pos i j (List.ofOption update) := by
  simpa using εClosure'.step step .base

theorem εClosure'.trans {nfa : NFA} {s : String} {pos : ValidPos s} {i j k update₁ update₂}
  (cls₁ : εClosure' nfa pos i j update₁) (cls₂ : εClosure' nfa pos j k update₂) :
  εClosure' nfa pos i k (update₁ ++ update₂) := by
  induction cls₁ with
  | base => exact cls₂
  | step step rest ih =>
    simp
    exact .step step (ih cls₂)

theorem εClosure'.snoc {nfa : NFA} {s : String} {pos : ValidPos s} {i j k update₁ update₂}
  (cls : εClosure' nfa pos i j update₁) (step : nfa.εStep' pos j k update₂) :
  εClosure' nfa pos i k (update₁ ++ List.ofOption update₂) :=
  cls.trans (εClosure'.single step)

theorem εClosure'_of_path {nfa : NFA} {s : String} {pos : ValidPos s} {i j pos' updates}
  (wf : nfa.WellFormed) (hpos : pos = pos') (path : nfa.Path 0 i pos j pos' updates) :
  nfa.εClosure' pos ⟨i, path.lt⟩ ⟨j, path.lt_right wf⟩ updates := by
  induction path with
  | last step =>
    subst hpos
    exact εClosure'.single step
  | @more i pos j pos' k pos'' update₁ update₂ step rest ih =>
    match step.eq_or_next with
    | .inl hpos' =>
      subst hpos hpos'
      simp at ih
      exact .step (by simp [εStep', step]) ih
    | .inr ⟨_, hpos'⟩ =>
      subst hpos hpos'
      exact ((Nat.not_le_of_lt pos.lt_next) rest.le).elim

theorem εClosure'_iff_path {s : String} (nfa : NFA) (wf : nfa.WellFormed) (i j : Fin nfa.nodes.size) (pos : ValidPos s) (updates : List (Nat × ValidPos s)) :
  nfa.εClosure' pos i j updates ↔ (i = j ∧ updates = []) ∨ nfa.Path 0 i pos j pos updates := by
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
