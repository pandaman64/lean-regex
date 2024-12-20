-- When the regex matches a string, the compiled NFA accepts it.
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Transition.Path.Basic

import Mathlib.Tactic.Common

namespace Regex.NFA

theorem pathIn_of_matches.group {cs : List Char}
  (eq : pushRegex nfa next (.group i e) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next e = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs) :
  pathIn result nfa.nodes.size result.val.start next cs := by
  open Compile.ProofData Group in
  let pd := Group.intro eq
  simp [pd.eq_result eq]

  have wf_close := pd.wf_close assm₁ assm₂
  have wf' := pd.wf' assm₁ assm₂

  have pathClose : nfaClose.pathIn nfa.nodes.size pd.nfa.nodes.size next [] := by
    refine .last (.εStep (Nat.le_refl _) nfaClose_property ?_)
    simp [pd.get_close_pre, Node.εStep]
    rfl
  have pathClose : nfa'.pathIn nfa.nodes.size nfa.nodes.size next [] := by
    apply pathClose.cast
    intro i _ h₂
    exact ⟨Nat.lt_trans h₂ size_lt_close', (pd.get_lt_close h₂).symm⟩
  have pathExpr : nfaExpr.pathIn nfaClose.nodes.size nfaExpr.start nfaClose.start cs :=
    ih rfl wf_close wf_close.start_lt
  have pathExpr : nfaExpr.pathIn nfa.nodes.size nfaExpr.start nfaClose.start cs :=
    pathExpr.castBound (Nat.le_of_lt nfaClose_property)
  have pathExpr : nfa'.pathIn nfa.nodes.size nfaExpr.start nfaClose.start cs := by
    apply pathExpr.cast
    intro i _ h₂
    exact ⟨Nat.lt_trans h₂ size_lt_expr', (pd.get_lt_expr h₂).symm⟩
  have pathOpen : nfa'.pathIn nfa.nodes.size nfa'.start nfaExpr.start [] := by
    refine .last (.εStep (ge_pushRegex_start rfl) wf'.start_lt ?_)
    simp [pd.start_eq, pd.get_open, Node.εStep]

  have path := pathOpen.trans (pathExpr.trans pathClose)
  simp at path
  exact path

theorem pathIn_of_matches.alternateLeft {cs : List Char}
  (eq : pushRegex nfa next (.alternate e₁ e₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next e₁ = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs) :
  pathIn result nfa.nodes.size result.val.start next cs := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [pd.eq_result eq]

  have wf' := pd.wf' assm₁ assm₂

  have path₁ : nfa₁.pathIn nfa.nodes.size nfa₁.start next cs := ih rfl assm₁ assm₂
  have path₁ : nfa'.pathIn nfa.nodes.size nfa₁.start next cs := by
    apply path₁.cast
    intro i _ h₂
    exact ⟨Nat.lt_trans h₂ size_lt₁, (get_lt₁ h₂).symm⟩
  refine path₁.more (.εStep (ge_pushRegex_start rfl) wf'.start_lt ?_)
  show nfa₁.start ∈ (nfa'[nfa'.start]'wf'.start_lt).εStep
  simp [pd.get_start, Node.εStep]

theorem pathIn_of_matches.alternateRight {cs : List Char}
  (eq : pushRegex nfa next (.alternate e₁ e₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next e₂ = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs) :
  pathIn result nfa.nodes.size result.val.start next cs := by
  open Compile.ProofData Alternate in
  let pd := Alternate.intro eq
  simp [pd.eq_result eq]

  have wf₁ := pd.wf₁ assm₁ assm₂
  have wf' := pd.wf' assm₁ assm₂

  have path₂ : nfa₂.pathIn nfa₁.nodes.size nfa₂.start next cs := ih rfl wf₁ (Nat.lt_trans assm₂ nfa₁_property)
  have path₂ : nfa'.pathIn nfa₁.nodes.size nfa₂.start next cs := by
    apply path₂.cast
    intro i _ h₂
    exact ⟨Nat.lt_trans h₂ size_lt₂, (get_lt₂ h₂).symm⟩
  have path₂ : nfa'.pathIn nfa.nodes.size nfa₂.start next cs :=
    path₂.castBound (Nat.le_of_lt nfa₁_property)
  refine path₂.more (.εStep (ge_pushRegex_start rfl) wf'.start_lt ?_)
  show nfa₂.start ∈ (nfa'[nfa'.start]'wf'.start_lt).εStep
  simp [pd.get_start, Node.εStep]

theorem pathIn_of_matches.concat {cs₁ cs₂ : List Char}
  (eq : pushRegex nfa next (.concat e₁ e₂) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (ih₁ : ∀ {nfa next nfa'}, pushRegex nfa next e₁ = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs₁)
  (ih₂ : ∀ {nfa next nfa'}, pushRegex nfa next e₂ = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs₂) :
  pathIn result nfa.nodes.size result.val.start next (cs₁ ++ cs₂) := by
  open Compile.ProofData Concat in
  let pd := Concat.intro eq
  simp [pd.eq_result eq]

  have wf₂ := pd.wf₂ assm₁ assm₂

  have ih₂ : nfa₂.pathIn nfa.nodes.size nfa₂.start next cs₂ := ih₂ rfl assm₁ assm₂
  have ih₂ : nfa'.pathIn nfa.nodes.size nfa₂.start next cs₂ := by
    apply ih₂.cast
    intro i _ h₂
    exact ⟨Nat.lt_trans h₂ size₂_lt, (get_lt₂ h₂).symm⟩
  have ih₁ : nfa'.pathIn nfa₂.nodes.size nfa'.start nfa₂.start cs₁ :=
    ih₁ (Subtype.eq eq_push.symm) wf₂ wf₂.start_lt
  exact (ih₁.castBound (Nat.le_of_lt nfa₂_property)).trans ih₂

theorem pathIn_of_matches.starConcat {cs₁ cs₂ : List Char}
  (eq : pushRegex nfa next (.star e) = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (ih₁ : ∀ {nfa next nfa'}, pushRegex nfa next e = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs₁)
  (ih₂ : ∀ {nfa next nfa'}, pushRegex nfa next (.star e) = nfa' →
    nfa.WellFormed →
    next < nfa.nodes.size →
    pathIn nfa' nfa.nodes.size nfa'.val.start next cs₂) :
  pathIn result nfa.nodes.size result.val.start next (cs₁ ++ cs₂) := by
  open Compile.ProofData Star in
  let pd := Star.intro eq
  simp [pd.eq_result eq]

  have wf_placeholder := pd.wf_placeholder assm₁
  have wf' := pd.wf' assm₁ assm₂

  have pathStart : nfa'.pathIn nfa.nodes.size nfa'.start nfaExpr.start [] := by
    refine .last (.εStep (ge_pushRegex_start rfl) wf'.start_lt ?_)
    simp [pd.start_eq, pd.get_start, Node.εStep]
  have pathExpr : nfaExpr.pathIn nfaPlaceholder.nodes.size nfaExpr.start nfaPlaceholder.start cs₁ :=
    ih₁ rfl wf_placeholder wf_placeholder.start_lt
  have pathExpr : nfa'.pathIn nfaPlaceholder.nodes.size nfaExpr.start nfaPlaceholder.start cs₁ := by
    apply pathExpr.cast
    intro i h₁ h₂
    simp [nfaPlaceholder] at h₁
    have h₂ := pd.size_eq_expr' ▸ h₂

    have get := pd.get i h₂
    have not_lt : ¬(i < pd.nfa.nodes.size) := by omega
    have ne : i ≠ pd.nfa.nodes.size := by omega
    simp [not_lt, ne] at get
    exact ⟨h₂, get.symm⟩
  have pathExpr : nfa'.pathIn nfa.nodes.size nfaExpr.start nfaPlaceholder.start cs₁ :=
    pathExpr.castBound (Nat.le_of_lt nfaPlaceholder_property)
  have pathLoop : nfa'.pathIn nfa.nodes.size nfa'.start next cs₂ := ih₂ rfl assm₁ assm₂

  have path := pathStart.trans (pathExpr.trans pathLoop)
  simp at path
  exact path

theorem pathIn_of_matches (eq : pushRegex nfa next e = result)
  (assm₁ : nfa.WellFormed) (assm₂ : next < nfa.nodes.size)
  (m : e.matches cs) :
  pathIn result nfa.nodes.size result.val.start next cs := by
  open Compile.ProofData in
  induction m generalizing nfa next with
  | char c =>
    let pd := Char.intro eq
    simp [pd.eq_result eq]
    refine .last (.charStep (ge_pushRegex_start rfl) (pd.wf' assm₁ assm₂).start_lt ?_)
    simp [pd.start_eq, pd.get_eq, Node.charStep]
    exact ⟨rfl, rfl⟩
  | sparse cls c hmem =>
    let pd := Classes.intro eq
    simp [pd.eq_result eq]
    refine .last (.charStep (ge_pushRegex_start rfl) (pd.wf' assm₁ assm₂).start_lt ?_)
    simp [pd.start_eq, pd.get_eq, Node.charStep]
    exact ⟨hmem, rfl⟩
  | epsilon =>
    let pd := Epsilon.intro eq
    simp [pd.eq_result eq]
    refine .last (.εStep (ge_pushRegex_start rfl) (pd.wf' assm₁ assm₂).start_lt ?_)
    simp [pd.start_eq, pd.get_eq, Node.εStep]
    rfl
  | group _ ih => exact pathIn_of_matches.group eq assm₁ assm₂ ih
  | alternateLeft _ ih => exact pathIn_of_matches.alternateLeft eq assm₁ assm₂ ih
  | alternateRight _ ih => exact pathIn_of_matches.alternateRight eq assm₁ assm₂ ih
  | concat cs₁ cs₂ r₁ r₂ _ _ ih₁ ih₂ => exact pathIn_of_matches.concat eq assm₁ assm₂ ih₁ ih₂
  | starEpsilon =>
    let pd := Star.intro eq
    simp [pd.eq_result eq]
    refine .last (.εStep (ge_pushRegex_start rfl) (pd.wf' assm₁ assm₂).start_lt ?_)
    simp [pd.start_eq, pd.get_start, Node.εStep]
    exact .inr rfl
  | starConcat cs₁ cs₂ r _ _ ih₁ ih₂ => exact pathIn_of_matches.starConcat eq assm₁ assm₂ ih₁ ih₂

theorem pathIn_of_compile_matches (eq : compile r = nfa)
  (m : r.matches cs) :
  pathIn nfa 1 nfa.start 0 cs := by
  unfold NFA.compile at eq
  set result := NFA.done.pushRegex 0 r with h
  have := pathIn_of_matches h.symm done_WellFormed (by simp [done]) m
  rw [eq] at this
  exact this

end Regex.NFA
