import RegexCorrectness.NFA.Semantics.ProofData.Basic
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

open String (ValidPos)

namespace Regex.NFA

variable {s : String} {nfa : NFA} {next e result lb} {pos pos' : ValidPos s} {i j update}

@[grind →]
theorem Step.eq_or_lt_of_pushNode {node} (step : (nfa.pushNode node).Step lb i pos j pos' update) :
  i = nfa.nodes.size ∨ i < nfa.nodes.size ∧ nfa.Step lb i pos j pos' update := by
  grind

@[grind →]
theorem Step.eq_or_lt_of_pushRegex (step : (nfa.pushRegex next e).Step lb i pos j pos' update) :
  nfa.nodes.size ≤ i ∨ i < nfa.nodes.size ∧ nfa.Step lb i pos j pos' update := by
  fun_induction pushRegex <;> grind [pushRegex_size_lt]

@[grind →]
theorem Step.eq_or_ge_of_pushRegex
  (step : (nfa.pushRegex next e).Step nfa.nodes.size i pos j pos' update) :
  j = next ∨ nfa.nodes.size ≤ j := by
  fun_induction pushRegex <;> grind [pushRegex_size_lt]

theorem Path.eq_or_path_next (eq : nfa.pushRegex next e = result)
  (jlt : j < nfa.nodes.size) (ige : i ≥ nfa.nodes.size)
  (path : result.Path lb i pos j pos' update) :
  j = next ∨
  ∃ posm update₁ update₂,
    update = update₁ ++ update₂ ∧
    result.Path nfa.nodes.size i pos next posm update₁ ∧
    result.Path lb next posm j pos' update₂ := by
  induction path with
  | @last i pos j pos' update step =>
    have step := eq ▸ step.liftBound' ige
    have := step.eq_or_ge_of_pushRegex
    omega
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
  (jlt : j < nfa.nodes.size) (ige : i ≥ nfa.nodes.size) (ne : j ≠ next)
  (path : result.Path lb i pos j pos' update) :
  ∃ posm update₁ update₂,
    update = update₁ ++ update₂ ∧
    result.Path nfa.nodes.size i pos next posm update₁ ∧
    result.Path lb next posm j pos' update₂ := by
  have := path.eq_or_path_next eq jlt ige
  cases this with
  | inl eq => contradiction
  | inr h => exact h

end Regex.NFA
