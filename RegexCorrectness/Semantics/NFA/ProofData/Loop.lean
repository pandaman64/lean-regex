import RegexCorrectness.Semantics.NFA.ProofData.Basic
import RegexCorrectness.Semantics.NFA.ProofData.Cast

open Regex.NFA.Semantics (Span Heap)

set_option autoImplicit false

namespace Regex.NFA.Compile.ProofData.Star

variable [Star]

inductive Loop : Span → Heap → Span → Heap → Prop where
  | last {span heap} (step : nfa'.Step nfa.nodes.size nfa'.start span heap next span heap) : Loop span heap span heap
  | loop {span heap span' heap' span'' heap''}
    (path : nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span heap nfaPlaceholder.start span' heap')
    (loop : Loop span' heap' span'' heap'') : Loop span heap span'' heap''

theorem Loop.introAux {i span heap j span' heap'}
  (lt : i < nfa'.nodes.size) (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) (eqj : j = next)
  (path : nfa'.Path nfa.nodes.size i span heap j span' heap') :
  if i = nfa'.start then
    (nfa'.Step nfa.nodes.size nfa'.start span heap next span' heap' ∧ span' = span ∧ heap' = heap) ∨
    (∃ spanm heapm,
      nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span heap nfaPlaceholder.start spanm heapm ∧
      Loop spanm heapm span' heap')
  else
    ∃ spanm heapm,
      nfa'.Path nfaPlaceholder.nodes.size i span heap nfaPlaceholder.start spanm heapm ∧
      Loop spanm heapm span' heap' := by
  induction path with
  | @last i span heap j span' heap' step =>
    split
    next eqi =>
      subst eqi eqj
      simp [step_start_iff] at step
      simp [step]

      have wf' := wf' wf next_lt
      have : nfa'[nfa'.start]'wf'.start_lt = .split nfaExpr.start next := by
        simp [start_eq, get_start]

      exact .inl (.splitRight (Nat.le_of_eq start_eq.symm) wf'.start_lt this)
    next nei =>
      have : nfa.nodes.size ≤ i := step.ge
      have : i ≠ nfa.nodes.size := start_eq ▸ nei
      have gt : i > nfa.nodes.size := by omega

      have step : nfa'.Step (nfa.nodes.size + 1) i span heap j span' heap' :=
        step.liftBound' gt
      have step : nfa'.Step nfaPlaceholder.nodes.size i span heap j span' heap' := by
        simp [nfaPlaceholder, step]
      have step : nfaExpr.Step nfaPlaceholder.nodes.size i span heap j span' heap' :=
        step.cast (get_ne_start i step.lt (Nat.ne_of_gt gt))

      have := step.eq_or_ge_of_pushRegex
      simp [nfaPlaceholder, eqj] at this
      omega
  | @more i span heap j span' heap' k span'' heap'' step rest ih =>
    have ih' := ih rest.lt eqj
    split
    next eqi =>
      subst eqi eqj
      have : j ≠ next := by
        have : nfa.nodes.size ≤ j := rest.ge
        omega
      simp [step_start_iff, this] at step

      have ne : nfaExpr.start ≠ nfa'.start := by
        have : nfaPlaceholder.nodes.size ≤ nfaExpr.start := ge_pushRegex_start rfl
        simp [nfaPlaceholder] at this
        simp [start_eq]
        omega
      simp [step, ne] at ih'

      exact .inr ih'
    next nei =>
      have gt : i > nfa.nodes.size := by
        simp [start_eq] at nei
        have := step.ge
        omega
      split at ih'
      next eqj =>
        match ih' with
        | .inl ⟨step', hspan, hheap⟩ =>
          simp [hspan, hheap, eqj] at *
          refine ⟨span', heap', ?_, .last step'⟩
          simp [nfaPlaceholder]

          have path := Path.last (step.liftBound' gt)
          exact start_eq ▸ path
        | .inr ⟨spanm, heapm, path', loop'⟩ =>
          have loop'' := Loop.loop path' loop'
          refine ⟨span', heap', ?_, loop''⟩
          simp [nfaPlaceholder]

          have step : nfa'.Step nfa.nodes.size i span heap nfa.nodes.size span' heap' :=
            have : j = nfa.nodes.size := eqj ▸ start_eq
            this ▸ step
          exact (.last (step.liftBound' gt))
      next nej =>
        have ⟨spanm, heapm, path', loop'⟩ := ih'
        have step : nfa'.Step nfaPlaceholder.nodes.size i span heap j span' heap' := by
          simp [nfaPlaceholder]
          exact step.liftBound' gt
        exact ⟨spanm, heapm, .more step path', loop'⟩

theorem Loop.intro {span heap span' heap'}
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa'.start span heap next span' heap') :
  Loop span heap span' heap' := by
  have wf' := wf' wf next_lt
  have loop := introAux wf'.start_lt wf next_lt rfl path
  simp at loop
  match loop with
  | .inl ⟨step, hspan, hheap⟩ =>
    simp [hspan, hheap] at *
    exact .last step
  | .inr ⟨span'', heap'', path, loop⟩ => exact Loop.loop path loop

end Regex.NFA.Compile.ProofData.Star
