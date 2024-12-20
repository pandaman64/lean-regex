import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

namespace Regex.NFA.Compile.ProofData

namespace Empty

variable [Empty] {lb span heap j span' heap'}

theorem not_step_start : ¬nfa'.Step lb nfa'.start span heap j span' heap' := by
  have : nfa'[nfa'.start]'(by simp [size_eq, start_eq]) = .fail := by
    simp [start_eq, get_eq]
  intro step
  cases step <;> simp [this] at *

theorem not_path_start : ¬nfa'.Path lb nfa'.start span heap j span' heap' := by
  intro path
  cases path with
  | last step => exact not_step_start step
  | more step => exact not_step_start step

end Empty

namespace Epsilon

variable [Epsilon] {span heap j span' heap'}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start span heap j span' heap' ↔
  j = next ∧ span' = span ∧ heap' = heap := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .epsilon next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hspan, hheap⟩
    simp_all
    exact .epsilon (by simp [start_eq]) lt this

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start span heap j span' heap' ↔
  j = next ∧ span' = span ∧ heap' = heap := by
  apply Iff.intro
  . intro path
    cases path with
    | last step => exact step_start_iff.mp step
    | more step rest =>
      simp [step_start_iff] at step
      simp [step] at rest
      have ge := rest.ge
      omega
  . simp [←step_start_iff]
    exact .last

end Epsilon

namespace Char

variable [Char] {span heap j span' heap'}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start span heap j span' heap' ↔
  ∃ r', span.r = c :: r' ∧ j = next ∧ span' = ⟨span.l, c :: span.m, r'⟩ ∧ heap' = heap := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .char c next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨r', hr, hj, hspan, hheap⟩
    simp_all
    have : nfa'.Step nfa.nodes.size nfa'.start ⟨span.l, span.m, c :: r'⟩ heap next ⟨span.l, c :: span.m, r'⟩ heap :=
      .char (by simp [start_eq]) lt this
    simp [←hr] at this
    exact this

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start span heap j span' heap' ↔
  ∃ r', span.r = c :: r' ∧ j = next ∧ span' = ⟨span.l, c :: span.m, r'⟩ ∧ heap' = heap := by
  apply Iff.intro
  . intro path
    cases path with
    | last step => exact step_start_iff.mp step
    | more step rest =>
      simp [step_start_iff] at step
      have ⟨_, step⟩ := step
      simp [step] at rest
      have ge := rest.ge
      omega
  . simp [←step_start_iff]
    exact .last

end Char

namespace Classes

variable [Classes] {span heap j span' heap'}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start span heap j span' heap' ↔
  ∃ c r', span.r = c :: r' ∧ c ∈ cs ∧ j = next ∧ span' = ⟨span.l, c :: span.m, r'⟩ ∧ heap' = heap := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_eq, start_eq]
  have : nfa'[nfa'.start] = .sparse cs next := by
    simp [start_eq, get_eq]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
    next mem _ => exact ⟨_, _, (by simp), mem, rfl, rfl⟩
  . intro ⟨c, r', hr, mem, hj, hspan, hheap⟩
    simp_all
    have : nfa'.Step nfa.nodes.size nfa'.start ⟨span.l, span.m, c :: r'⟩ heap next ⟨span.l, c :: span.m, r'⟩ heap :=
      .sparse (by simp [start_eq]) lt this mem
    simp [←hr] at this
    exact this

theorem path_start_iff (next_lt : next < nfa.nodes.size) :
  nfa'.Path nfa.nodes.size nfa'.start span heap j span' heap' ↔
  ∃ c r', span.r = c :: r' ∧ c ∈ cs ∧ j = next ∧ span' = ⟨span.l, c :: span.m, r'⟩ ∧ heap' = heap := by
  apply Iff.intro
  . intro path
    cases path with
    | last step => exact step_start_iff.mp step
    | more step rest =>
      simp [step_start_iff] at step
      have ⟨_, _, step⟩ := step
      simp [step] at rest
      have ge := rest.ge
      omega
  . simp [←step_start_iff]
    exact .last

end Classes

namespace Group

variable [Group] {span heap j span' heap'}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start span heap j span' heap' ↔
  j = nfaExpr.start ∧ span' = span ∧ heap' = heap[2 * tag := span.curr] := by
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt_expr', start_eq]
  have : nfa'[nfa'.start] = .save (2 * tag) nfaExpr.start := by
    simp [start_eq, get_open]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hspan, hheap⟩
    simp_all
    exact .save (ge_pushRegex_start rfl) lt this

end Group

namespace Alternate

variable [Alternate] {span heap j span' heap'}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start span heap j span' heap' ↔
  (j = nfa₁.start ∨ j = nfa₂.start) ∧ span' = span ∧ heap' = heap := by
  have ge : nfa.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt₂, start_eq]
  have : nfa'[nfa'.start] = .split nfa₁.start nfa₂.start := get_start
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hspan, hheap⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt this
    | inr hj =>
      simp_all
      exact .splitRight ge lt this

end Alternate

namespace Star

variable [Star] {span heap j span' heap'}

theorem step_start_iff :
  nfa'.Step nfa.nodes.size nfa'.start span heap j span' heap' ↔
  (j = nfaExpr.start ∨ j = next) ∧ span' = span ∧ heap' = heap := by
  have ge : nfa.nodes.size ≤ nfa'.start := ge_pushRegex_start rfl
  have lt : nfa'.start < nfa'.nodes.size := by
    simp [size_lt, start_eq]
  have : nfa'[nfa'.start] = .split nfaExpr.start next := by
    simp [start_eq, get_start]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨hj, hspan, hheap⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt this
    | inr hj =>
      simp_all
      exact .splitRight ge lt this

end Star

end Regex.NFA.Compile.ProofData
