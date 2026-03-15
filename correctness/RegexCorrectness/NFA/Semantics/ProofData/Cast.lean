module

public import RegexCorrectness.NFA.Semantics.Path

open String (Pos)

public section

namespace Regex.NFA

namespace Compile.ProofData

namespace Group

variable [Group] {s : String} {pos pos' : Pos s} {update}

theorem castFromExpr (path : nfaExpr.Path nfaClose.size nfaExpr.start pos nfaClose.start pos' update) :
  nfa'.Path nfaClose.size nfaExpr.start pos nfaClose.start pos' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt_expr', by grind⟩

theorem castToExpr {lb j} (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : nfa'.Path lb nfaExpr.start pos j pos' update) :
  nfaExpr.Path lb nfaExpr.start pos j pos' update := by
  have wfExpr := wfExpr wf next_lt
  apply path.cast' wfExpr.start_lt (Nat.le_of_lt size_lt_expr') wfExpr
  intro i _ lt
  grind

end Group

namespace Alternate

variable [Alternate] {s : String} {pos pos' : Pos s} {update}

theorem castFrom₁ (path : nfa₁.Path nfa.size nfa₁.start pos next pos' update) :
  nfa'.Path nfa.size nfa₁.start pos next pos' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt₁, by grind⟩

theorem castFrom₂ (path : nfa₂.Path nfa.size nfa₂.start pos next pos' update) :
  nfa'.Path nfa.size nfa₂.start pos next pos' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size_lt₂, by grind⟩

theorem castTo₁ (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : nfa'.Path nfa.size nfa₁.start pos next pos' update) :
  nfa₁.Path nfa.size nfa₁.start pos next pos' update := by
  have wf₁ := wf₁ wf next_lt
  apply path.cast' wf₁.start_lt (Nat.le_of_lt size_lt₁) wf₁
  intro i _ lt
  grind

theorem castTo₂ {lb} (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : nfa'.Path lb nfa₂.start pos next pos' update) :
  nfa₂.Path lb nfa₂.start pos next pos' update := by
  have wf₂ := wf₂ wf next_lt
  apply path.cast' wf₂.start_lt (Nat.le_of_lt size_lt₂) wf₂
  intro i _ lt
  grind

end Alternate

namespace Concat

variable [Concat] {s : String} {pos pos' : Pos s} {update}

theorem castFrom₂ (path : nfa₂.Path nfa.size nfa₂.start pos next pos' update) :
  nfa'.Path nfa.size nfa₂.start pos next pos' update := by
  apply path.cast
  intro i _ lt
  exact ⟨Nat.lt_trans lt size₂_lt, by grind⟩

theorem castTo₂ (wf : nfa.WellFormed) (next_lt : next < nfa.size)
  (path : nfa'.Path nfa.size nfa₂.start pos next pos' update) :
  nfa₂.Path nfa.size nfa₂.start pos next pos' update := by
  have wf₂ := wf₂ wf next_lt
  apply path.cast' wf₂.start_lt (Nat.le_of_lt size₂_lt) wf₂
  intro i _ lt
  grind

end Concat

namespace Star

variable [Star] {s : String} {pos pos' : Pos s} {update}

theorem castFromExpr (path : nfaExpr.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start pos' update) :
  nfa'.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start pos' update := by
  apply path.cast
  intro i ge lt
  simp [nfaPlaceholder] at ge
  exact ⟨by grind, by grind⟩

theorem castToExpr (wf : nfa.WellFormed)
  (path : nfa'.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start pos' update) :
  nfaExpr.Path nfaPlaceholder.size nfaExpr.start pos nfaPlaceholder.start pos' update := by
  have wfExpr := wfExpr wf
  apply path.cast' wfExpr.start_lt (by grind) wfExpr
  intro i ge lt
  simp [nfaPlaceholder] at ge
  grind

end Star

end Compile.ProofData

end Regex.NFA

end
