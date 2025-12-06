import RegexCorrectness.NFA.Semantics.ProofData.Basic
import RegexCorrectness.NFA.Semantics.ProofData.Compile

set_option autoImplicit false

open String (ValidPos)

namespace Regex.NFA.Compile.ProofData.Star

variable [Star]

/--
Consider `nfa' := nfa.pushRegex next e`. When there is a path in `nfa'` from `nfa'.start` to `next`,
it must have looped `nfaExpr` before `n` times, followed by the last step from `nfa'.start` to `next`.

A `Loop` term corresponds to such a loop. The `last` variant corresponds to the last step,
and the `loop` variant extracts the first iteration and the remaining loop.
-/
inductive Loop {s : String} : ValidPos s → ValidPos s → List (Nat × ValidPos s) → Prop where
  | last {pos} (step : nfa'.Step nfa.nodes.size nfa'.start pos next pos .none) : Loop pos pos []
  | loop {pos pos' pos'' update₁ update₂}
    (path : nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start pos nfaPlaceholder.start pos' update₁)
    (loop : Loop pos' pos'' update₂) : Loop pos pos'' (update₁ ++ update₂)

theorem Loop.introAux {s : String} {pos pos' : ValidPos s} {i j update}
  (lt : i < nfa'.nodes.size) (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) (eqj : j = next)
  (path : nfa'.Path nfa.nodes.size i pos j pos' update) :
  if i = nfa'.start then
    (nfa'.Step nfa.nodes.size nfa'.start pos next pos' .none ∧ pos' = pos ∧ update = []) ∨
    (∃ posm update₁ update₂,
      nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start pos nfaPlaceholder.start posm update₁ ∧
      Loop posm pos' update₂ ∧
      update = update₁ ++ update₂)
  else
    ∃ posm update₁ update₂,
      nfa'.Path nfaPlaceholder.nodes.size i pos nfaPlaceholder.start posm update₁ ∧
      Loop posm pos' update₂ ∧
      update = update₁ ++ update₂ := by
  induction path with
  | @last i pos j pos' update step =>
    split
    next eqi =>
      subst eqi eqj
      simp only [step_start_iff, or_true, true_and] at step
      simp only [step, List.ofOption_none, and_self, and_true, List.nil_eq, List.append_eq_nil_iff,
        exists_and_left, ↓existsAndEq, exists_eq_right_right]

      have wf' := wf' wf next_lt
      have : nfa'[nfa'.start]'wf'.start_lt = splitNode := by
        simp [start_eq, get_start]
      simp only [splitNode] at this

      split at this
      . exact .inl (.splitRight (Nat.le_of_eq start_eq.symm) wf'.start_lt this)
      . exact .inl (.splitLeft (Nat.le_of_eq start_eq.symm) wf'.start_lt this)
    next nei =>
      have : nfa.nodes.size ≤ i := step.ge
      have : i ≠ nfa.nodes.size := start_eq ▸ nei
      have gt : i > nfa.nodes.size := by grind

      have step : nfa'.Step (nfa.nodes.size + 1) i pos j pos' update :=
        step.liftBound' gt
      have step : nfa'.Step nfaPlaceholder.nodes.size i pos j pos' update := by
        simp [nfaPlaceholder, step]
      have step : nfaExpr.Step nfaPlaceholder.nodes.size i pos j pos' update :=
        step.cast (get_ne_start i step.lt (Nat.ne_of_gt gt))

      have := step.eq_or_ge_of_pushRegex
      simp only [eqj, nfaPlaceholder, pushNode_start_eq, pushNode_size] at this
      grind
  | @more i pos j pos' k pos'' update₁ update₂ step rest ih =>
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
        | .inl ⟨step', hpos, hupdate⟩ =>
          simp [hpos, hupdate, eqj] at *
          refine ⟨pos', List.ofOption update₁, ?_, [], .last step', by simp⟩
          simp [nfaPlaceholder]

          have path := Path.last (step.liftBound' gt)
          exact start_eq ▸ path
        | .inr ⟨itm, update₃, update₄, path', loop', equ⟩ =>
          have loop'' := Loop.loop path' loop'
          refine ⟨pos', List.ofOption update₁, update₃ ++ update₄, ?_, loop'', by simp [equ]⟩
          simp [nfaPlaceholder]

          have step : nfa'.Step nfa.nodes.size i pos nfa.nodes.size pos' update₁ :=
            have : j = nfa.nodes.size := eqj ▸ start_eq
            this ▸ step
          exact (.last (step.liftBound' gt))
      next nej =>
        have ⟨itm, update₃, update₄, path', loop', equ⟩ := ih'
        have step : nfa'.Step nfaPlaceholder.nodes.size i pos j pos' update₁ := by
          simp [nfaPlaceholder]
          exact step.liftBound' gt
        exact ⟨itm, update₁ ::ₒ update₃, update₄, .more step path', loop', by simp [equ]⟩

theorem Loop.intro {s : String} {pos pos' : ValidPos s} {update}
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa'.start pos next pos' update) :
  Loop pos pos' update := by
  have wf' := wf' wf next_lt
  have loop := introAux wf'.start_lt wf next_lt rfl path
  simp at loop
  match loop with
  | .inl ⟨step, hpos, hupdate⟩ =>
    simp [hpos, hupdate] at *
    exact .last step
  | .inr ⟨pos'', update₁, path, update₂, loop, equ⟩ => exact equ ▸ Loop.loop path loop

end Regex.NFA.Compile.ProofData.Star
