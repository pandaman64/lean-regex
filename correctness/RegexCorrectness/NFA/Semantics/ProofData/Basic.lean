import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

open String (ValidPos)

namespace Regex.NFA.Compile.ProofData

namespace Empty

variable [Empty] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem not_step_start : ¬nfa'.Step lb nfa'.start p j p' update := by
  have : nfa'[nfa'.start]'(by simp [size_eq, start_eq]) = .fail := by
    simp [start_eq, get_eq]
  intro step
  cases step <;> simp [this] at *

theorem not_path_start : ¬nfa'.Path lb nfa'.start p j p' update := by
  intro path
  cases path with
  | last step => exact not_step_start step
  | more step => exact not_step_start step

end Empty

namespace Epsilon

variable [Epsilon] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = .none := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .epsilon next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate⟩
    simp_all
    exact .epsilon (by simp [start_eq]) lt this

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = [] := by
  apply Iff.intro
  . intro path
    cases path with
    | last step =>
      simp [step_start_iff] at step
      simp [step]
    | more step rest =>
      simp [step_start_iff] at step
      simp [step] at rest
      have ge := rest.ge
      omega
  . intro ⟨hj, hp, hupdate⟩
    simp_all
    exact .last (step_start_iff.mpr ⟨rfl, rfl, rfl⟩)

end Epsilon

namespace Anchor

variable [Anchor] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = .none ∧ anchor.test p := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .anchor anchor next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate, hcond⟩
    simp_all
    exact .anchor (by simp [start_eq]) lt this hcond

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = [] ∧ anchor.test p := by
  apply Iff.intro
  . intro path
    cases path with
    | last step =>
      simp [step_start_iff] at step
      simp [step]
    | more step rest =>
      simp [step_start_iff] at step
      simp [step] at rest
      have ge := rest.ge
      omega
  . intro ⟨hj, hp, hupdate, hcond⟩
    simp_all
    exact .last (step_start_iff.mpr ⟨rfl, rfl, rfl, hcond⟩)

end Anchor

namespace Char

variable [Char] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ update = .none ∧ ∃ ne, p' = p.next ne ∧ p.get ne = c := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .char c next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    grind
  . intro ⟨hj, hupdate, ne, hp, hget⟩
    simp_all
    exact .char (by simp [start_eq]) lt this ne hget

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ update = [] ∧ ∃ ne, p' = p.next ne ∧ p.get ne = c := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .char c next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro path
    cases path with
    | last step =>
      simp [step_start_iff] at step
      simp [step]
    | more step rest =>
      simp [step_start_iff] at step
      simp [step] at rest
      have ge := rest.ge
      grind
  . intro ⟨hj, hupdate, ne, hp, hget⟩
    simp [hj, hupdate]
    exact .last (step_start_iff.mpr ⟨rfl, rfl, ne, hp, hget⟩)

end Char

namespace Classes

variable [Classes] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ update = .none ∧ ∃ ne, p' = p.next ne ∧ p.get ne ∈ cs := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .sparse cs next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    grind
  . intro ⟨hj, hupdate, ne, hp, mem⟩
    simp_all
    exact .sparse (by simp [start_eq]) lt this ne mem

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start p j p' update ↔
  j = next ∧ update = [] ∧ ∃ ne, p' = p.next ne ∧ p.get ne ∈ cs := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .sparse cs next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro path
    cases path with
    | last step =>
      simp [step_start_iff] at step
      simp [step]
    | more step rest =>
      simp [step_start_iff] at step
      simp [step] at rest
      have ge := rest.ge
      grind
  . intro ⟨hj, hupdate, ne, hp, mem⟩
    simp [hj, hupdate]
    exact .last (step_start_iff.mpr ⟨rfl, rfl, ne, hp, mem⟩)

end Classes

namespace Group

variable [Group] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  j = nfaExpr.start ∧ p' = p ∧ update = .some (2 * tag, p) := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt_expr', start_eq]
  have : nfa'[nfa'.start] = .save (2 * tag) nfaExpr.start := by
    simp [start_eq, get_open]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate⟩
    simp_all
    exact .save (ge_pushRegex_start rfl) lt this

theorem step_close_iff :
  nfa'.Step nfa.nodes.size nfaClose.start p j p' update ↔
  j = next ∧ p' = p ∧ update = .some (2 * tag + 1, p) := by
  have lt : nfaClose.start < nfa'.nodes.size := by
    simp [nfaClose, size_lt]
  have : nfa'[nfaClose.start] = .save (2 * tag + 1) next := by
    simp [nfaClose, get_close]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate⟩
    simp_all
    exact .save (by simp [nfaClose]) lt this

end Group

namespace Alternate

variable [Alternate] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  (j = nfa₁.start ∨ j = nfa₂.start) ∧ p' = p ∧ update = .none := by
  have ge : nfa.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt₂, start_eq]
  have : nfa'[nfa'.start] = .split nfa₁.start nfa₂.start := get_start
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt this
    | inr hj =>
      simp_all
      exact .splitRight ge lt this

end Alternate

namespace Star

variable [Star] {s : String} {lb} {p p' : ValidPos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start p j p' update ↔
  (j = nfaExpr.start ∨ j = next) ∧ p' = p ∧ update = .none := by
  have ge : nfa.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt, start_eq]
  have : nfa'[nfa'.start] = splitNode := by
    simp [start_eq, get_start]
  simp [splitNode] at this
  apply Iff.intro
  . intro step
    cases step <;> grind
  . intro ⟨hj, hp, hupdate⟩
    cases hj with
    | inl hj =>
      simp_all
      split at this
      . exact .splitLeft ge lt this
      . exact .splitRight ge lt this
    | inr hj =>
      simp_all
      split at this
      . exact .splitRight ge lt this
      . exact .splitLeft ge lt this

end Star

end Regex.NFA.Compile.ProofData
