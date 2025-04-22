import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

namespace Regex.NFA.Compile.ProofData

namespace Empty

variable [Empty] {lb it j it' update}

theorem not_step_start : ¬nfa'.Step lb nfa'.start it j it' update := by
  have : nfa'[nfa'.start]'(by simp [size_eq, start_eq]) = .fail := by
    simp [start_eq, get_eq]
  intro step
  cases step <;> simp [this] at *

theorem not_path_start : ¬nfa'.Path lb nfa'.start it j it' update := by
  intro path
  cases path with
  | last step => exact not_step_start step
  | more step => exact not_step_start step

end Empty

namespace Epsilon

variable [Epsilon] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  j = next ∧ it' = it ∧ update = .none ∧ it.Valid := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .epsilon next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hit, hupdate, v⟩
    simp_all
    exact .epsilon (by simp [start_eq]) lt this v

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start it j it' update ↔
  j = next ∧ it' = it ∧ update = [] ∧ it.Valid := by
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
  . intro ⟨hj, hit, hupdate, v⟩
    simp_all
    exact .last (step_start_iff.mpr ⟨rfl, rfl, rfl, v⟩)

end Epsilon

namespace Anchor

variable [Anchor] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  j = next ∧ it' = it ∧ update = .none ∧ it.Valid ∧ anchor.test it := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .anchor anchor next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hit, hupdate, v, hcond⟩
    simp_all
    exact .anchor (by simp [start_eq]) lt this v hcond

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start it j it' update ↔
  j = next ∧ it' = it ∧ update = [] ∧ it.Valid ∧ anchor.test it := by
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
  . intro ⟨hj, hit, hupdate, v, hcond⟩
    simp_all
    exact .last (step_start_iff.mpr ⟨rfl, rfl, rfl, v, hcond⟩)

end Anchor

namespace Char

variable [Char] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  ∃ l r, j = next ∧ it' = it.next ∧ update = .none ∧ it.ValidFor l (c :: r) := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .char c next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step
    case char l c r ge lt vf hn =>
      simp_all
      exact ⟨l, r, this.1 ▸ vf⟩
    all_goals simp_all
  . intro ⟨l, r, hj, hit, hupdate, vf⟩
    simp_all
    exact .char (by simp [start_eq]) lt this vf

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start it j it' update ↔
  ∃ l r, j = next ∧ it' = it.next ∧ update = [] ∧ it.ValidFor l (c :: r) := by
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
  . intro ⟨l, r, hj, hit, hupdate, vf⟩
    simp_all
    exact .last (step_start_iff.mpr ⟨l, r, rfl, rfl, rfl, vf⟩)

end Char

namespace Classes

variable [Classes] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  ∃ l c r, j = next ∧ it' = it.next ∧ update = .none ∧ it.ValidFor l (c :: r) ∧ c ∈ cs := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .sparse cs next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step
    case sparse l c r cs ge lt mem vf hn =>
      simp [hn] at this
      exact ⟨l, c, r, this.2, rfl, rfl, vf, this.1 ▸ mem⟩
    all_goals simp_all
  . intro ⟨l, c, r, hj, hit, hupdate, vf, mem⟩
    simp_all
    exact .sparse (by simp [start_eq]) lt this vf mem

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start it j it' update ↔
  ∃ l c r, j = next ∧ it' = it.next ∧ update = [] ∧ it.ValidFor l (c :: r) ∧ c ∈ cs := by
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
  . intro ⟨l, c, r, hj, hit, hupdate, vf, mem⟩
    simp_all
    exact .last (step_start_iff.mpr ⟨l, c, r, rfl, rfl, rfl, vf, mem⟩)

end Classes

namespace Group

variable [Group] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  j = nfaExpr.start ∧ it' = it ∧ update = .some (2 * tag, it.pos) ∧ it.Valid := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt_expr', start_eq]
  have : nfa'[nfa'.start] = .save (2 * tag) nfaExpr.start := by
    simp [start_eq, get_open]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hit, hupdate, v⟩
    simp_all
    exact .save (ge_pushRegex_start rfl) lt this v

theorem step_close_iff :
  nfa'.Step nfa.nodes.size nfaClose.start it j it' update ↔
  j = next ∧ it' = it ∧ update = .some (2 * tag + 1, it.pos) ∧ it.Valid := by
  have lt : nfaClose.start < nfa'.nodes.size := by
    simp [nfaClose, size_lt]
  have : nfa'[nfaClose.start] = .save (2 * tag + 1) next := by
    simp [nfaClose, get_close]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hit, hupdate, v⟩
    simp_all
    exact .save (by simp [nfaClose]) lt this v

end Group

namespace Alternate

variable [Alternate] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  (j = nfa₁.start ∨ j = nfa₂.start) ∧ it' = it ∧ update = .none ∧ it.Valid := by
  have ge : nfa.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt₂, start_eq]
  have : nfa'[nfa'.start] = .split nfa₁.start nfa₂.start := get_start
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hit, hupdate, v⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt this v
    | inr hj =>
      simp_all
      exact .splitRight ge lt this v

end Alternate

namespace Star

variable [Star] {it j it' update}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start it j it' update ↔
  (j = nfaExpr.start ∨ j = next) ∧ it' = it ∧ update = .none ∧ it.Valid := by
  have ge : nfa.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt, start_eq]
  have : nfa'[nfa'.start] = .split nfaExpr.start next := by
    simp [start_eq, get_start]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hit, hupdate, v⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt this v
    | inr hj =>
      simp_all
      exact .splitRight ge lt this v

end Star

end Regex.NFA.Compile.ProofData
