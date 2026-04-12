module

public import RegexCorrectness.NFA.Semantics.Path

open String (Pos)

public section

namespace Regex.NFA

variable {s : String} {nfa : NFA} {next e result lb} {pos pos' : Pos s} {i j update}

@[grind →]
theorem Step.eq_or_lt_of_pushNode {node} (step : (nfa.pushNode node).Step lb i pos j pos' update) :
  i = nfa.size ∨ i < nfa.size ∧ nfa.Step lb i pos j pos' update := by
  grind

@[grind →]
theorem Step.eq_or_lt_of_pushRegex (step : (nfa.pushRegex next e).Step lb i pos j pos' update) :
  nfa.size ≤ i ∨ i < nfa.size ∧ nfa.Step lb i pos j pos' update := by
  fun_induction pushRegex
  case case9 nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    cases Nat.lt_or_ge i nfa.size with
    | inl lt =>
      refine .inr ⟨lt, ?_⟩
      have : (pushRegex nfa next (.star greedy e))[i]'(by grind) = nfa[i] := by grind
      exact step.cast this
    | inr ge => exact .inl ge
  all_goals grind

@[grind →]
theorem Step.eq_or_ge_of_pushRegex
  (step : (nfa.pushRegex next e).Step nfa.size i pos j pos' update) :
  j = next ∨ nfa.size ≤ j := by
  fun_induction pushRegex
  next => grind
  next => grind
  next => grind
  next => grind
  next => grind
  next => grind
  next => grind
  next => grind
  case case9 nfa next greedy e patchAt placeholder compiled split quest patched ih =>
    let pd := Compile.ProofData.Star.intro' nfa next greedy e
    have of_get_eq_split (get : pd.nfa'[i]'step.lt = pd.split) : j = next ∨ nfa.size ≤ j := by
      unfold Compile.ProofData.Star.split at get
      split at get
      next =>
        have ⟨_, h, _⟩ := (Step.iff_split get).mp step
        cases h with
        | inl h => exact .inr (show pd.nfa.size ≤ j by grind)
        | inr h => exact .inl h
      next =>
        have ⟨_, h, _⟩ := (Step.iff_split get).mp step
        cases h with
        | inl h => exact .inl h
        | inr h => exact .inr (show pd.nfa.size ≤ j by grind)

    have get := pd.get i step.lt
    split_ifs at get
    next lt => exact (Nat.not_le_of_lt lt step.ge).elim
    next => exact of_get_eq_split get
    next =>
      have step' : pd.nfa'.Step nfa.size i pos j pos' update := step
      have stepExpr : pd.nfaExpr.Step nfa.size i pos j pos' update := step'.cast get
      cases ih (stepExpr.liftBound' (show pd.nfaPlaceholder.size ≤ i by grind)) with
      | inl eq => grind only
      | inr le => grind only [= pushNode_size]
    next => exact of_get_eq_split get

theorem Path.eq_or_path_next (eq : nfa.pushRegex next e = result)
  (jlt : j < nfa.size) (ige : i ≥ nfa.size)
  (path : result.Path lb i pos j pos' update) :
  j = next ∨
  ∃ posm update₁ update₂,
    update = update₁ ++ update₂ ∧
    result.Path nfa.size i pos next posm update₁ ∧
    result.Path lb next posm j pos' update₂ := by
  induction path with
  | @last i pos j pos' update step =>
    have step := eq ▸ step.liftBound' ige
    have := step.eq_or_ge_of_pushRegex
    grind [NFA.size]
  | @more i pos j pos' k pos'' update updates step rest ih =>
    have step := step.liftBound' ige
    cases (eq ▸ step).eq_or_ge_of_pushRegex with
    | inl jeq =>
      simp [jeq] at *
      exact .inr ⟨pos', List.ofOption update, updates, by simp, .last step, rest⟩
    | inr jge =>
      match ih jlt jge with
      | .inl keq => exact .inl keq
      | .inr ⟨itm, update₁, update₂, equ, path₁, path₂⟩ =>
        exact .inr ⟨itm, update ::ₒ update₁, update₂, by simp [equ], .more step path₁, path₂⟩

theorem Path.path_next_of_ne (eq : nfa.pushRegex next e = result)
  (jlt : j < nfa.size) (ige : i ≥ nfa.size) (ne : j ≠ next)
  (path : result.Path lb i pos j pos' update) :
  ∃ posm update₁ update₂,
    update = update₁ ++ update₂ ∧
    result.Path nfa.size i pos next posm update₁ ∧
    result.Path lb next posm j pos' update₂ := by
  have := path.eq_or_path_next eq jlt ige
  cases this with
  | inl eq => contradiction
  | inr h => exact h

end Regex.NFA

end
