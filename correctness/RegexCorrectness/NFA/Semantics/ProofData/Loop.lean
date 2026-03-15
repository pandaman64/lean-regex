module

public import RegexCorrectness.NFA.Semantics.ProofData.Basic
import RegexCorrectness.NFA.Semantics.ProofData.Compile

open String (Pos)

namespace Regex.NFA.Compile.ProofData.Star

variable [Star]

/--
Consider `nfa' := nfa.pushRegex next (.star greedy e)`. When there is a path in `nfa'` from `nfaExpr.start` to `next`,
it must have looped `nfaExpr` before `n` times, followed by the last step from `nfa.size` to `next`.

A `Loop` term corresponds to such a loop. The `last` variant corresponds to the last step,
and the `loop` variant extracts the first iteration and the remaining loop.
-/
public inductive Loop {s : String} : Pos s → Pos s → List (Nat × Pos s) → Prop where
  | last {pos} (step : nfa'.Step nfa.size nfa.size pos next pos .none) : Loop pos pos []
  | loop {pos pos' pos'' update₁ update₂}
    (path : nfa'.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start pos' update₁)
    (loop : Loop pos' pos'' update₂) :
    Loop pos pos'' (update₁ ++ update₂)

theorem Loop.introAux {s : String} {pos pos' : Pos s} {i j update}
  (lt : i < nfaExpr.size) (wf : nfa.WellFormed) (next_lt : next < nfa.size) (eqj : j = next)
  (path : nfa'.Path nfa.size i pos j pos' update) :
  if i = nfa.size then
    (nfa'.Step nfa.size nfa.size pos next pos' .none ∧ pos' = pos ∧ update = []) ∨
    (∃ posm update₁ update₂,
      nfa'.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start posm update₁ ∧
      Loop posm pos' update₂ ∧
      update = update₁ ++ update₂)
  else
    ∃ posm update₁ update₂,
      nfa'.Path nfaPlaceholder.size i pos nfaPlaceholder.start posm update₁ ∧
      Loop posm pos' update₂ ∧
      update = update₁ ++ update₂ := by
  induction path with
  | @last i pos j pos' update step =>
    have get := get i (by grind)
    split_ifs at get
    next => grind
    next eqi =>
      simp only [eqi, ↓reduceIte]
      cases step
      case splitLeft k ge lt' eq =>
        simp only [eqi, eqj] at eq
        exact .inl ⟨.splitLeft (Nat.le_refl _) size_lt eq, rfl, rfl⟩
      case splitRight k ge lt' eq =>
        simp only [eqi, eqj] at eq
        exact .inl ⟨.splitRight (Nat.le_refl _) size_lt eq, rfl, rfl⟩
      all_goals grind
    next ne =>
      have stepExpr : nfaExpr.Step nfa.size i pos j pos' update := step.cast get
      have stepExpr' : nfaExpr.Step nfaPlaceholder.size i pos j pos' update := stepExpr.liftBound' (by grind)
      grind [stepExpr'.eq_or_ge_of_pushRegex]
  | @more i pos j pos' k pos'' update₁ update₂ step rest ih =>
    have get := get i (by grind)
    split_ifs at get
    next => grind
    next eqi =>
      simp only [eqi, ↓reduceIte]
      if hg : greedy then
        cases _x : step
        case splitLeft l ge lt' eq =>
          simp only [eq, split, hg, ↓reduceIte, Node.split.injEq] at get
          have ih := ih (by grind) eqj
          simp only [show j ≠ nfa.size by grind, ↓reduceIte] at ih
          obtain ⟨posm, update₃, update₄, path', loop', equ⟩ := ih
          exact .inr ⟨posm, update₃, update₄, get.1 ▸ path', loop', by simp [equ]⟩
        all_goals grind
      else
        cases step
        case splitRight l ge lt' eq =>
          simp only [eq, split, hg, Bool.false_eq_true, ↓reduceIte, Node.split.injEq] at get
          have ih := ih (by grind) eqj
          simp only [show j ≠ nfa.size by grind, ↓reduceIte] at ih
          obtain ⟨posm, update₃, update₄, path', loop', equ⟩ := ih
          exact .inr ⟨posm, update₃, update₄, get.2 ▸ path', loop', by simp [equ]⟩
        all_goals grind
    next nei =>
      simp only [nei, ↓reduceIte]
      have step : nfa'.Step nfaPlaceholder.size i pos j pos' update₁ := step.liftBound' (by grind)
      have stepExpr := step.cast get
      have ih := ih (stepExpr.lt_right (wfExpr wf)) eqj
      split at ih
      next eqj =>
        match ih with
        | .inl ⟨step', hpos, hupdate⟩ =>
          subst pos'' update₂ j
          exact ⟨pos', List.ofOption update₁, [], .last (by grind), .last step', by simp⟩
        | .inr ⟨posm, update₃, update₄, path', loop', equ⟩ =>
          have := Loop.loop path' loop'
          exact ⟨pos', List.ofOption update₁, update₃ ++ update₄, .last (by grind), .loop path' loop', by simp [equ]⟩
      next nej =>
        obtain ⟨posm, update₃, update₄, path', loop', equ⟩ := ih
        have := Path.more step path'
        exact ⟨posm, update₁ ::ₒ update₃, update₄, .more step path', loop', by simp [equ]⟩

public theorem Loop.intro {s : String} {pos pos' : Pos s} {update}
  (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : nfa'.Path nfa.size nfaExpr.start pos next pos' update) :
  Loop pos pos' update := by
  have loop := introAux (by grind) wf next_lt rfl path
  split at loop
  next => grind
  next =>
    obtain ⟨posm, update₁, update₂, path', loop', equ⟩ := loop
    exact equ ▸ Loop.loop path' loop'

end Regex.NFA.Compile.ProofData.Star
