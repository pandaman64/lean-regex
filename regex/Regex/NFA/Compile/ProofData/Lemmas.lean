import Regex.NFA.Compile.Basic
import Regex.NFA.Compile.ProofData.Basic

open Regex.Data (Expr)

set_option autoImplicit false

namespace Regex.NFA

theorem pushNode_wf {nfa : NFA} {node}
  (wf : nfa.WellFormed) (inBounds : node.inBounds (nfa.nodes.size + 1)) :
  (nfa.pushNode node).WellFormed := by
  simp [pushNode, WellFormed.iff, NFA.get_eq_nodes_get]
  intro i
  cases Nat.lt_or_ge i.val nfa.nodes.size with
  | inl lt =>
    have : (nfa.nodes.push node)[i.val] = nfa.nodes[i.val] := nfa.nodes.getElem_push_lt _ _ lt
    simp [this]
    apply Node.inBounds_of_inBounds_of_le (wf.inBounds ⟨i.val, lt⟩) (by omega)
  | inr ge =>
    have isLt := i.isLt
    simp at isLt
    have : i.val = nfa.nodes.size := by omega
    simp [this, inBounds]

open Compile.ProofData in
theorem pushRegex_wf {nfa : NFA} {next e}
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) :
  (nfa.pushRegex next e).WellFormed := by
  induction e generalizing nfa next with
  | empty =>
    simp [pushRegex]
    exact pushNode_wf wf (by simp)
  | epsilon =>
    simp [pushRegex]
    apply pushNode_wf wf
    exact Nat.lt_trans next_lt (by omega)
  | anchor a =>
    simp [pushRegex]
    apply pushNode_wf wf
    exact Nat.lt_trans next_lt (by omega)
  | char c =>
    simp [pushRegex]
    apply pushNode_wf wf
    exact Nat.lt_trans next_lt (by omega)
  | classes cs =>
    simp [pushRegex]
    apply pushNode_wf wf
    exact Nat.lt_trans next_lt (by omega)
  | group tag e ih =>
    let pd := Group.intro' nfa next tag e

    have wf_close : (pd.nfaClose).WellFormed := by
      apply pushNode_wf wf
      simp [Node.inBounds]
      exact Nat.lt_trans next_lt (by omega)

    have wf_expr : (pd.nfaExpr).WellFormed := ih wf_close wf_close.start_lt

    apply pushNode_wf wf_expr
    exact Nat.lt_trans wf_expr.start_lt (by omega)
  | alternate e₁ e₂ ih₁ ih₂ =>
    let pd := Alternate.intro' nfa next e₁ e₂

    have wf₁ : (pd.nfa₁).WellFormed := ih₁ wf next_lt
    have wf₂ : (pd.nfa₂).WellFormed := ih₂ wf₁ (Nat.lt_trans next_lt pd.nfa₁_property)

    apply pushNode_wf wf₂
    simp [Node.inBounds]
    exact ⟨
      Nat.lt_trans wf₁.start_lt (Nat.lt_trans pd.nfa₂_property (by omega)),
      Nat.lt_trans wf₂.start_lt (by omega)
    ⟩
  | concat e₁ e₂ ih₁ ih₂ =>
    let pd := Concat.intro' nfa next e₁ e₂

    have wf₂ : (pd.nfa₂).WellFormed := ih₂ wf next_lt
    apply ih₁ wf₂ wf₂.start_lt
  | star e ih =>
    let pd := Star.intro' nfa next e
    show (pd.nfa').WellFormed

    have wf_placeholder : (pd.nfaPlaceholder).WellFormed := by
      apply pushNode_wf wf
      simp
    have wf_expr : (pd.nfaExpr).WellFormed :=
      ih wf_placeholder pd.nfaPlaceholder_property

    simp [WellFormed.iff]
    refine ⟨pd.size_lt, ?_⟩
    intro i
    cases Nat.decEq i pd.nfa.nodes.size with
    | isTrue eq =>
      simp [eq]
      simp [pd.get_start, Node.inBounds]
      exact ⟨pd.size_eq_expr' ▸ wf_expr.start_lt, Nat.lt_trans next_lt size_lt⟩
    | isFalse ne =>
      simp [pd.get_ne_start i i.isLt ne, pd.size_eq_expr']
      exact wf_expr.inBounds ⟨i, pd.size_eq_expr' ▸ i.isLt⟩

theorem compile_wf {e} : (compile e).WellFormed := by
  simp [compile]
  apply pushRegex_wf done_WellFormed (by simp [done])

-- Well-formedness of the NFAs
namespace Compile.ProofData

theorem Empty.wf' [Empty] (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

theorem Epsilon.wf' [Epsilon] (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

theorem Char.wf' [Char] (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

theorem Classes.wf' [Classes] (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

namespace Group

variable [Group]

theorem wf_close (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfaClose.WellFormed := by
  apply pushNode_wf wf
  simp [Node.inBounds]
  omega

theorem wf_expr (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfaExpr.WellFormed :=
  pushRegex_wf (wf_close wf next_lt) (wf_close wf next_lt).start_lt

theorem wf' (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

end Group

namespace Alternate

variable [Alternate]

theorem wf₁ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa₁.WellFormed :=
  pushRegex_wf wf next_lt

theorem wf₂ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa₂.WellFormed :=
  pushRegex_wf (wf₁ wf next_lt) (Nat.lt_trans next_lt nfa₁_property)

theorem wf' (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

end Alternate

namespace Concat

variable [Concat]

theorem wf₂ (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa₂.WellFormed :=
  pushRegex_wf wf next_lt

theorem wf' (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

end Concat

namespace Star

variable [Star]

theorem wf_placeholder (wf : nfa.WellFormed) : nfaPlaceholder.WellFormed := by
  apply pushNode_wf wf
  simp

theorem wf_expr (wf : nfa.WellFormed) : nfaExpr.WellFormed :=
  pushRegex_wf (wf_placeholder wf) (wf_placeholder wf).start_lt

theorem wf' (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) : nfa'.WellFormed :=
  pushRegex_wf wf next_lt

end Star

end Compile.ProofData

end Regex.NFA
