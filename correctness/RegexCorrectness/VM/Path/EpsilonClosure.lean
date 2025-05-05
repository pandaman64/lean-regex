import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (Pos Iterator)

-- Transition relations specialized for ε-closure traversal.
namespace Regex.NFA

def εStep' (nfa : NFA) (it : Iterator) (i j : Fin nfa.nodes.size) (update : Option (Nat × Pos)) : Prop :=
  nfa.Step 0 i it j it update

section

variable {nfa : NFA} {it i j update}

theorem εStep'.done (hn : nfa[i] = .done) :
  nfa.εStep' it i j update ↔ False := by
  apply Step.iff_done hn

theorem εStep'.fail (hn : nfa[i] = .fail) :
  nfa.εStep' it i j update ↔ False := by
  apply Step.iff_fail hn

theorem εStep'.epsilon {next : Nat} (hn : nfa[i] = .epsilon next) :
  nfa.εStep' it i j update ↔ j = next ∧ update = .none ∧ it.Valid := by
  simp [εStep', Step.iff_epsilon hn]

theorem εStep'.anchor {anchor} {next : Nat} (hn : nfa[i] = .anchor anchor next) :
  nfa.εStep' it i j update ↔ j = next ∧ update = .none ∧ it.Valid ∧ anchor.test it := by
  simp [εStep', Step.iff_anchor hn]

theorem εStep'.split {next₁ next₂ : Nat} (hn : nfa[i] = .split next₁ next₂) :
  nfa.εStep' it i j update ↔ (j = next₁ ∨ j = next₂) ∧ update = .none ∧ it.Valid := by
  simp [εStep', Step.iff_split hn]

theorem εStep'.save {offset} {next : Nat} (hn : nfa[i] = .save offset next) :
  nfa.εStep' it i j update ↔ j = next ∧ update = .some (offset, it.pos) ∧ it.Valid := by
  simp [εStep', Step.iff_save hn]

theorem εStep'.char {c} {next : Nat} (hn : nfa[i] = .char c next) :
  nfa.εStep' it i j update ↔ False := by
  simp [εStep', Step.iff_char hn]

theorem εStep'.sparse {cs} {next : Nat} (hn : nfa[i] = .sparse cs next) :
  nfa.εStep' it i j update ↔ False := by
  simp [εStep', Step.iff_sparse hn]

theorem εStep'.valid (step : nfa.εStep' it i j update) : it.Valid := step.validL

end

inductive εClosure' (nfa : NFA) (it : Iterator) : Fin nfa.nodes.size → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | base {i} (v : it.Valid) : εClosure' nfa it i i []
  | step {i j k update₁ update₂} (step : nfa.εStep' it i j update₁) (rest : εClosure' nfa it j k update₂) :
    εClosure' nfa it i k (update₁ ::ₒ update₂)

theorem εClosure'.single {nfa : NFA} {it i j update} (step : nfa.εStep' it i j update) :
  εClosure' nfa it i j (List.ofOption update) := by
  simpa using εClosure'.step step (εClosure'.base step.valid)

theorem εClosure'.trans {nfa : NFA} {it i j k update₁ update₂}
  (cls₁ : εClosure' nfa it i j update₁) (cls₂ : εClosure' nfa it j k update₂) :
  εClosure' nfa it i k (update₁ ++ update₂) := by
  induction cls₁ with
  | base => exact cls₂
  | step step rest ih =>
    simp
    exact .step step (ih cls₂)

theorem εClosure'.snoc {nfa : NFA} {it i j k update₁ update₂}
  (cls : εClosure' nfa it i j update₁) (step : nfa.εStep' it j k update₂) :
  εClosure' nfa it i k (update₁ ++ List.ofOption update₂) :=
  cls.trans (εClosure'.single step)

theorem εClosure'_of_path {nfa : NFA} {i j it it' updates} (wf : nfa.WellFormed) (hit : it = it')
  (path : nfa.Path 0 i it j it' updates) :
  nfa.εClosure' it ⟨i, path.lt⟩ ⟨j, path.lt_right wf⟩ updates := by
  induction path with
  | last step =>
    subst hit
    exact εClosure'.single step
  | @more i it j it' k it'' update₁ update₂ step rest ih =>
    match step.it_eq_or_next with
    | .inl hit' =>
      subst hit hit'
      simp at ih
      exact .step (by simp [εStep', step]) ih
    | .inr ⟨_, hit'⟩ =>
      subst hit hit'
      exact ((Nat.not_le_of_lt it.lt_next) rest.le_pos).elim

theorem εClosure'_iff_path (nfa : NFA) (wf : nfa.WellFormed) (i j : Fin nfa.nodes.size) (it : Iterator) (updates : List (Nat × Pos)) :
  nfa.εClosure' it i j updates ↔ (i = j ∧ updates = [] ∧ it.Valid) ∨ nfa.Path 0 i it j it updates := by
  apply Iff.intro
  . intro cls
    induction cls with
    | base v => simp [v]
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

theorem εClosure'.valid {nfa : NFA} {it i j updates} (cls : nfa.εClosure' it i j updates) : it.Valid := by
  cases cls with
  | base v => exact v
  | step step rest => exact step.valid

end Regex.NFA
