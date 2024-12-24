import RegexCorrectness.NFA.Semantics.ProofData.Basic

set_option autoImplicit false

namespace Regex.NFA

namespace Compile.ProofData

namespace Group

variable [Group] {span span' update}

theorem castFromExpr (path : nfaExpr.Path nfaClose.nodes.size nfaExpr.start span nfaClose.start span' update) :
  nfa'.Path nfaClose.nodes.size nfaExpr.start span nfaClose.start span' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt_expr', (get_lt_expr lt).symm⟩

theorem castToExpr (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfaClose.nodes.size nfaExpr.start span nfaClose.start span' update) :
  nfaExpr.Path nfaClose.nodes.size nfaExpr.start span nfaClose.start span' update := by
  have wf_expr := wf_expr wf next_lt
  apply path.cast' wf_expr.start_lt (Nat.le_of_lt size_lt_expr') wf_expr
  intro i _ lt
  exact get_lt_expr lt

end Group

namespace Alternate

variable [Alternate] {span span' update}

theorem castFrom₁ (path : nfa₁.Path nfa.nodes.size nfa₁.start span next span' update) :
  nfa'.Path nfa.nodes.size nfa₁.start span next span' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt₁, (get_lt₁ lt).symm⟩

theorem castFrom₂ (path : nfa₂.Path nfa.nodes.size nfa₂.start span next span' update) :
  nfa'.Path nfa.nodes.size nfa₂.start span next span' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt₂, (get_lt₂ lt).symm⟩

theorem castTo₁ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa₁.start span next span' update) :
  nfa₁.Path nfa.nodes.size nfa₁.start span next span' update := by
  have wf₁ := wf₁ wf next_lt
  apply path.cast' wf₁.start_lt (Nat.le_of_lt size_lt₁) wf₁
  intro i _ lt
  exact get_lt₁ lt

theorem castTo₂ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa₁.nodes.size nfa₂.start span next span' update) :
  nfa₂.Path nfa₁.nodes.size nfa₂.start span next span' update := by
  have wf₂ := wf₂ wf next_lt
  apply path.cast' wf₂.start_lt (Nat.le_of_lt size_lt₂) wf₂
  intro i _ lt
  exact get_lt₂ lt

end Alternate

namespace Concat

variable [Concat] {span span' update}

theorem castFrom₂ (path : nfa₂.Path nfa.nodes.size nfa₂.start span next span' update) :
  nfa'.Path nfa.nodes.size nfa₂.start span next span' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size₂_lt, (get_lt₂ lt).symm⟩

theorem castTo₂ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size)
  (path : nfa'.Path nfa.nodes.size nfa₂.start span next span' update) :
  nfa₂.Path nfa.nodes.size nfa₂.start span next span' update := by
  have wf₂ := wf₂ wf next_lt
  apply path.cast' wf₂.start_lt (Nat.le_of_lt size₂_lt) wf₂
  intro i _ lt
  exact get_lt₂ lt

end Concat

namespace Star

variable [Star] {span span' update}

theorem castFromExpr (path : nfaExpr.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start span' update) :
  nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start span' update := by
  apply path.cast
  intro i ge lt
  simp [nfaPlaceholder] at ge
  exact ⟨size_eq_expr' ▸ lt, (get_ne_start i (size_eq_expr' ▸ lt) (Nat.ne_of_gt ge)).symm⟩

theorem castToExpr (wf : nfa.WellFormed)
  (path : nfa'.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start span' update) :
  nfaExpr.Path nfaPlaceholder.nodes.size nfaExpr.start span nfaPlaceholder.start span' update := by
  have wf_expr := wf_expr wf
  apply path.cast' wf_expr.start_lt (Nat.le_of_eq size_eq_expr'.symm) wf_expr
  intro i ge lt
  simp [nfaPlaceholder] at ge
  exact (get_ne_start i (size_eq_expr' ▸ lt) (Nat.ne_of_gt ge))

end Star

end Compile.ProofData

end Regex.NFA
