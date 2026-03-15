-- TODO: rename to Path.lean
module

public import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Semantics.ProofData.Compile
import RegexCorrectness.NFA.Semantics.ProofData.Cast

open String (Pos)

public section

namespace Regex.NFA.Compile.ProofData

namespace Empty

variable [Empty] {s : String} {lb} {p p' : Pos s} {j update}

theorem not_step_start : ¬nfa'.Step lb nfa'.start p j p' update := by
  have : nfa'[nfa'.start]'(by simp [size_eq, start_eq]) = .fail := by
    grind only [= get, = start_eq]
  grind only [= start_eq, = size_eq, = Step.iff_fail]

theorem not_path_start : ¬nfa'.Path lb nfa'.start p j p' update := by
  intro path
  cases path with
  | last step => exact not_step_start step
  | more step => exact not_step_start step

end Empty

namespace Epsilon

variable [Epsilon] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = .none := by
  have : nfa'[nfa'.start]'(by grind only [= size_eq, = start_eq]) = .epsilon next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate⟩
    grind => instantiate only [= start_eq, = size_eq, Step.epsilon]

theorem path_start_iff (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = [] := by
  apply Iff.intro
  . intro path
    cases path with
    | last step =>
      obtain ⟨rfl, rfl, rfl⟩ := step_start_iff.mp step
      simp
    | more step rest =>
      obtain ⟨rfl, rfl, rfl⟩ := step_start_iff.mp step
      grind only [→ Path.ge]
  . intro ⟨eqj, eqp, equ⟩
    simpa only [eqj, eqp, equ] using .last (step_start_iff.mpr ⟨rfl, rfl, rfl⟩)

end Epsilon

namespace Anchor

variable [Anchor] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  j = next ∧ p' = p ∧ update = .none ∧ anchor.test p := by
  have lt : nfa'.start < nfa'.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .anchor anchor next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hp, hupdate, hcond⟩
    simp_all
    exact .anchor (by simp [start_eq]) lt this hcond

theorem path_start_iff (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p j p' update ↔
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

variable [Char] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  j = next ∧ update = .none ∧ ∃ ne, p' = p.next ne ∧ p.get ne = c := by
  have lt : nfa'.start < nfa'.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .char c next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    grind
  . intro ⟨hj, hupdate, ne, hp, hget⟩
    simp_all
    exact .char (by simp [start_eq]) lt this ne hget

theorem path_start_iff (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p j p' update ↔
  j = next ∧ update = [] ∧ ∃ ne, p' = p.next ne ∧ p.get ne = c := by
  have lt : nfa'.start < nfa'.size := by
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

variable [Classes] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  j = next ∧ update = .none ∧ ∃ ne, p' = p.next ne ∧ p.get ne ∈ cs := by
  have lt : nfa'.start < nfa'.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .sparse cs next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    grind
  . intro ⟨hj, hupdate, ne, hp, mem⟩
    simp_all
    exact .sparse (by simp [start_eq]) lt this ne mem

theorem path_start_iff (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p j p' update ↔
  j = next ∧ update = [] ∧ ∃ ne, p' = p.next ne ∧ p.get ne ∈ cs := by
  have lt : nfa'.start < nfa'.size := by
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

variable [Group] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  j = nfaExpr.start ∧ p' = p ∧ update = .some (2 * tag, p) := by
  grind

theorem step_close_iff :
  nfa'.Step nfa.size nfaClose.start p j p' update ↔
  j = next ∧ p' = p ∧ update = .some (2 * tag + 1, p) := by
  grind

theorem path_start_iff (wf : nfa.WellFormed) (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p next p' update ↔
  ∃ updates,
    update = (2 * tag, p) :: updates ++ [(2 * tag + 1, p')] ∧
    nfaExpr.Path nfaClose.size nfaExpr.start p nfaClose.start p' updates := by
  refine ⟨?_, ?_⟩
  . intro path
    cases path with
    | last step =>
      obtain ⟨h, rfl, rfl⟩ := step_start_iff.mp step
      grind only [= start, = nfaExpr, → Step.ge, = start_eq, = nfaClose, !pushRegex_size_lt, = pushNode_size]
    | more step rest =>
      obtain ⟨rfl, rfl, rfl⟩ := step_start_iff.mp step
      have rest := castToExpr wf next_lt rest
      obtain ⟨p', updates, updates', rfl, path, path'⟩ :=
        rest.path_next_of_ne (show nfaClose.pushRegex nfaClose.start e' = nfaExpr by grind) (by grind) (by grind) (by grind)
      cases path' with
      | last step' =>
        obtain ⟨_, rfl, rfl⟩ := step_close_iff.mp (step'.cast (lt := by grind) (by grind))
        exact ⟨updates, by simp, path⟩
      | more step' rest' =>
        obtain ⟨h, rfl, rfl⟩ := step_close_iff.mp (step'.cast (lt := by grind) (by grind))
        grind only [→ Path.ge]
  . intro ⟨updates, hupdate, path⟩
    have path : nfa'.Path nfa.size nfaExpr.start p nfaClose.start p' updates :=
      (castFromExpr path).liftBound (by grind)
    have path : nfa'.Path nfa.size nfa'.start p nfaClose.start p' ((2 * tag, p) :: updates) :=
      .more (step_start_iff.mpr ⟨rfl, rfl, rfl⟩) path
    have path : nfa'.Path nfa.size nfa'.start p next p' ((2 * tag, p) :: updates ++ [(2 * tag + 1, p')]) :=
      path.trans (.last (step_close_iff.mpr ⟨rfl, rfl, rfl⟩))
    simpa [hupdate] using path

end Group

namespace Alternate

variable [Alternate] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  (j = nfa₁.start ∨ j = nfa₂.start) ∧ p' = p ∧ update = .none := by
  grind

theorem path_start_iff (wf : nfa.WellFormed) (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p next p' update ↔
  nfa₁.Path nfa.size nfa₁.start p next p' update ∨ nfa₂.Path nfa.size nfa₂.start p next p' update := by
  refine ⟨?_, fun h => h.elim ?_ ?_⟩
  . intro path
    cases path with
    | last step =>
      obtain ⟨h, rfl, rfl⟩ := step_start_iff.mp step
      grind
    | more step path =>
      obtain ⟨h, rfl, rfl⟩ := step_start_iff.mp step
      cases h with
      | inl h =>
        subst h
        exact .inl (castTo₁ wf next_lt path)
      | inr h =>
        subst h
        exact .inr (castTo₂ wf next_lt path)
  . intro path₁
    have path₁ := castFrom₁ path₁
    exact .more (step_start_iff.mpr ⟨.inl rfl, rfl, rfl⟩) path₁
  . intro path₂
    have path₂ := castFrom₂ path₂
    exact .more (step_start_iff.mpr ⟨.inr rfl, rfl, rfl⟩) path₂

end Alternate

namespace Concat

variable [Concat] {s : String} {lb} {p p' : Pos s} {j update}

theorem path_start_iff (wf : nfa.WellFormed) (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p next p' update ↔
  ∃ pm updates₁ updates₂,
    update = updates₁ ++ updates₂ ∧
    nfa'.Path nfa₂.size nfa'.start p nfa₂.start pm updates₁ ∧
    nfa₂.Path nfa.size nfa₂.start pm next p' updates₂ := by
  refine ⟨?_, ?_⟩
  . intro path
    obtain ⟨pm, updates₁, updates₂, rfl, path₁, path₂⟩ :=
      path.path_next_of_ne (show nfa₂.pushRegex nfa₂.start e₁ = nfa' by grind) (by grind) (by grind) (by grind)
    exact ⟨pm, updates₁, updates₂, rfl, path₁, castTo₂ wf next_lt path₂⟩
  . intro ⟨pm, updates₁, updates₂, hupdate, path₁, path₂⟩
    simpa [hupdate] using (path₁.liftBound (by grind)).trans (castFrom₂ path₂)

end Concat

namespace Star

variable [Star] {s : String} {lb} {p p' : Pos s} {j update}

theorem step_start_iff :
  nfa'.Step nfa.size nfa'.start p j p' update ↔
  (j = nfaExpr.start ∨ j = next) ∧ p' = p ∧ update = .none := by
  apply Iff.intro
  . intro step
    cases step <;> grind
  . intro ⟨hj, hp, hupdate⟩
    subst p update
    have ge : nfa.size ≤ nfa'.start := by grind
    have lt : nfa'.start < nfa'.size := by grind
    if hg : greedy then
      have eq : nfa'[nfa'.start] = .split nfaExpr.start next := by grind
      cases hj with
      | inl hj => exact .splitLeft ge lt (hj ▸ eq)
      | inr hj => exact .splitRight ge lt (hj ▸ eq)
    else
      have eq : nfa'[nfa'.start] = .split next nfaExpr.start := by grind
      cases hj with
      | inl hj => exact .splitRight ge lt (hj ▸ eq)
      | inr hj => exact .splitLeft ge lt (hj ▸ eq)

theorem path_start_iff (next_lt : next < nfa.size) :
  nfa'.Path nfa.size nfa'.start p next p' update ↔
  (p' = p ∧ update = []) ∨ nfa'.Path nfa.size nfaExpr.start p next p' update := by
  refine ⟨?_, fun h => h.elim ?_ ?_⟩
  . intro path
    cases path with
    | last step =>
      obtain ⟨_, rfl, rfl⟩ := step_start_iff.mp step
      exact .inl ⟨rfl, rfl⟩
    | more step path =>
      obtain ⟨h, rfl, rfl⟩ := step_start_iff.mp step
      cases h with
      | inl h => exact .inr (h ▸ path)
      | inr h => grind
  . intro ⟨eqp, equ⟩
    subst p' update
    have step : nfa'.Step nfa.size nfa'.start p next p .none :=
      step_start_iff.mpr ⟨.inr rfl, rfl, rfl⟩
    exact .last step
  . intro path
    have step : nfa'.Step nfa.size nfa'.start p nfaExpr.start p .none :=
      step_start_iff.mpr ⟨.inl rfl, rfl, rfl⟩
    exact .more step path

end Star

end Regex.NFA.Compile.ProofData

end
