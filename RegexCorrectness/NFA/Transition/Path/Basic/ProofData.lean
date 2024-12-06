import RegexCorrectness.NFA.Transition.Path.Basic.Basic
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

-- Lemmas about the paths for the compiled NFAs.
namespace Regex.NFA.Compile.ProofData

namespace Group

variable [Group]

theorem stepIn_open_iff {j cs} :
  nfa'.stepIn nfa.nodes.size nfa'.start j cs ↔ j = nfaExpr.start ∧ cs = [] := by
  apply Iff.intro
  . intro step
    cases step with
    | charStep _ _ step => simp [start_eq, get_open, Node.charStep] at step
    | εStep _ _ step =>
      simp [start_eq, get_open, Node.εStep] at step
      simp [step]
  . intro ⟨h₁, h₂⟩
    subst h₁ h₂
    refine .εStep (start_eq ▸ Nat.le_of_lt (Nat.lt_trans nfaClose_property nfaExpr_property)) (start_eq ▸ size_lt_expr') ?_
    simp [start_eq, get_open, Node.εStep]

theorem stepIn_close_iff {j cs} :
  nfa'.stepIn nfa.nodes.size nfa.nodes.size j cs ↔ j = next ∧ cs = [] := by
  apply Iff.intro
  . intro step
    cases step with
    | charStep _ _ step => simp [get_close, Node.charStep] at step
    | εStep _ _ step =>
      simp [get_close, Node.εStep] at step
      simp [step]
  . intro ⟨h₁, h₂⟩
    subst h₁ h₂
    refine .εStep (Nat.le_refl _) size_lt ?_
    simp [get_close, Node.εStep]

end Group

namespace Alternate

variable [Alternate]

theorem stepIn_start_iff {j cs} :
  nfa'.stepIn nfa.nodes.size nfa'.start j cs ↔ (j = nfa₁.start ∨ j = nfa₂.start) ∧ cs = [] := by
  apply Iff.intro
  . intro step
    cases step with
    | charStep _ _ step => simp [get_start, Node.charStep] at step
    | εStep _ _ step =>
      simp [get_start, Node.εStep] at step
      simp [step]
  . intro ⟨h₁, h₂⟩
    subst h₂
    refine .εStep (start_eq ▸ (Nat.le_of_lt (Nat.lt_trans nfa₁_property nfa₂_property))) (start_eq ▸ size_lt₂) ?_
    simp [get_start, Node.εStep, h₁]

end Alternate

namespace Star

variable [Star]

theorem stepIn_start_iff {j cs} :
  nfa'.stepIn nfa.nodes.size nfa.nodes.size j cs ↔ (j = nfaExpr.start ∨ j = next) ∧ cs = [] := by
  apply Iff.intro
  . intro step
    cases step with
    | charStep _ _ step => simp [get_start, Node.charStep] at step
    | εStep _ _ step =>
      simp [get_start, Node.εStep] at step
      simp [step]
  . intro ⟨h₁, h₂⟩
    subst h₂
    refine .εStep (Nat.le_refl _) size_lt ?_
    simp [get_start, Node.εStep, h₁]

-- TODO: do we need `from_expr`?
theorem stepIn_to_expr {i j cs} (h : nfa.nodes.size < i)
  (step : nfa'.stepIn nfa.nodes.size i j cs) :
  nfaExpr.stepIn nfa.nodes.size i j cs := by
  apply step.cast
  . have get := Star.get i step.h₂
    have nlt := Nat.not_lt_of_ge step.h₁
    have ne := Nat.ne_of_gt h
    simp [nlt, ne] at get
    exact get

theorem of_stepIn {i j cs} (step : nfa'.stepIn nfa.nodes.size i j cs) :
  (i = nfa.nodes.size ∧ (j = nfaExpr.start ∨ j = next) ∧ cs = []) ∨
  (nfa.nodes.size < i ∧ nfaExpr.stepIn nfa.nodes.size i j cs) := by
  cases Nat.eq_or_lt_of_le step.h₁ with
  | inl eq =>
    subst eq
    have := stepIn_start_iff.mp step
    simp [this]
  | inr lt => exact .inr ⟨lt, stepIn_to_expr lt step⟩

end Star

end Regex.NFA.Compile.ProofData
