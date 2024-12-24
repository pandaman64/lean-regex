import RegexCorrectness.NFA.Semantics.ProofData.Basic
import RegexCorrectness.NFA.Semantics.ProofData.Compile

open Regex.Data (Span)

set_option autoImplicit false

namespace Regex.NFA.Compile.ProofData.Star

variable [Star]

/--
Consider `nfa' := nfa.pushRegex next e`. When there is a path in `nfa'` from `nfa'.start` to `next`,
it must have looped `nfaExpr` before `n` times, followed by the last step from `nfa'.start` to `next`.

A `Loop` term corresponds to such a loop. The `last` variant corresponds to the last step,
and the `loop` variant extracts the first iteration and the remaining loop.
-/
inductive Loop : Span → Span → List (Nat × String.Pos) → Prop where
  | last {span} (step : nfa'.Step nfa.nodes.size nfa'.start span next span .none) : Loop span span []
  | loop {span span' span'' update₁ update₂}
    (path : nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start span' update₁)
    (loop : Loop span' span'' update₂) : Loop span span'' (update₁ ++ update₂)

theorem Loop.introAux {i span j span' update}
  (lt : i < nfa'.nodes.size) (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) (eqj : j = next)
  (path : nfa'.Path nfa.nodes.size i span j span' update) :
  if i = nfa'.start then
    (nfa'.Step nfa.nodes.size nfa'.start span next span' .none ∧ span' = span ∧ update = []) ∨
    (∃ spanm update₁ update₂,
      nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start spanm update₁ ∧
      Loop spanm span' update₂ ∧
      update = update₁ ++ update₂)
  else
    ∃ spanm update₁ update₂,
      nfa'.Path nfaPlaceholder.nodes.size i span nfaPlaceholder.start spanm update₁ ∧
      Loop spanm span' update₂ ∧
      update = update₁ ++ update₂ := by
  induction path with
  | @last i span j span' update step =>
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

      have step : nfa'.Step (nfa.nodes.size + 1) i span j span' update :=
        step.liftBound' gt
      have step : nfa'.Step nfaPlaceholder.nodes.size i span j span' update := by
        simp [nfaPlaceholder, step]
      have step : nfaExpr.Step nfaPlaceholder.nodes.size i span j span' update :=
        step.cast (get_ne_start i step.lt (Nat.ne_of_gt gt))

      have := step.eq_or_ge_of_pushRegex
      simp [nfaPlaceholder, eqj] at this
      omega
  | @more i span j span' k span'' update₁ update₂ step rest ih =>
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
      simp [step]
      exact .inr ih'
    next nei =>
      have gt : i > nfa.nodes.size := by
        simp [start_eq] at nei
        have := step.ge
        omega
      split at ih'
      next eqj =>
        match ih' with
        | .inl ⟨step', hspan, hupdate⟩ =>
          simp [hspan, hupdate, eqj] at *
          refine ⟨span', List.ofOption update₁, ?_, [], .last step', by simp⟩
          simp [nfaPlaceholder]

          have path := Path.last (step.liftBound' gt)
          exact start_eq ▸ path
        | .inr ⟨spanm, update₃, update₄, path', loop', equ⟩ =>
          have loop'' := Loop.loop path' loop'
          refine ⟨span', List.ofOption update₁, update₃ ++ update₄, ?_, loop'', by simp [equ]⟩
          simp [nfaPlaceholder]

          have step : nfa'.Step nfa.nodes.size i span nfa.nodes.size span' update₁ :=
            have : j = nfa.nodes.size := eqj ▸ start_eq
            this ▸ step
          exact (.last (step.liftBound' gt))
      next nej =>
        have ⟨spanm, update₃, update₄, path', loop', equ⟩ := ih'
        have step : nfa'.Step nfaPlaceholder.nodes.size i span j span' update₁ := by
          simp [nfaPlaceholder]
          exact step.liftBound' gt
        exact ⟨spanm, update₁ ::ₒ update₃, update₄, .more step path', loop', by simp [equ]⟩

theorem Loop.intro {span span' update}
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa'.start span next span' update) :
  Loop span span' update := by
  have wf' := wf' wf next_lt
  have loop := introAux wf'.start_lt wf next_lt rfl path
  simp at loop
  match loop with
  | .inl ⟨step, hspan, hupdate⟩ =>
    simp [hspan, hupdate] at *
    exact .last step
  | .inr ⟨span'', update₁, path, update₂, loop, equ⟩ => exact equ ▸ Loop.loop path loop

end Regex.NFA.Compile.ProofData.Star
