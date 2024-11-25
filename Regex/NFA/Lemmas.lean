import Regex.NFA.Compile

open Regex.Data (Expr)

namespace Regex.NFA

theorem pushNode_wf {nfa : NFA} {node result} (eq : result = nfa.pushNode node)
  (wf : nfa.WellFormed) (inBounds : node.inBounds (nfa.nodes.size + 1)) :
  result.val.WellFormed := by
  simp [eq, pushNode, WellFormed.iff, NFA.get_eq_nodes_get]
  intro i
  cases Nat.lt_or_ge i.val nfa.nodes.size with
  | inl lt =>
    have : (nfa.nodes.push node)[i.val] = nfa.nodes[i.val] := nfa.nodes.get_push_lt _ _ lt
    simp [this]
    apply Node.inBounds_of_inBounds_of_le (wf.inBounds ⟨i.val, lt⟩) (by omega)
  | inr ge =>
    have isLt := i.isLt
    simp at isLt
    have : i.val = nfa.nodes.size := by omega
    simp [this, inBounds]

theorem pushRegex_wf {nfa : NFA} {next e result} (eq : nfa.pushRegex next e = result)
  (wf : nfa.WellFormed) (next_lt : next < nfa.nodes.size) :
  result.val.WellFormed := by
  induction e generalizing nfa next with
  | empty =>
    apply pushRegex.empty eq
    intro eq
    apply pushNode_wf eq wf
    simp
  | epsilon =>
    apply pushRegex.epsilon eq
    intro eq
    apply pushNode_wf eq wf
    simp [Node.inBounds]
    omega
  | char c =>
    apply pushRegex.char eq
    intro eq
    apply pushNode_wf eq wf
    simp [Node.inBounds]
    omega
  | classes cs =>
    apply pushRegex.sparse eq
    intro eq
    apply pushNode_wf eq wf
    simp [Node.inBounds]
    omega
  | group tag e ih =>
    apply pushRegex.group eq
    intro nfa' nfa'' nfa''' isLt eq₁ eq₂ eq₃ eq₄
    simp [eq₄]

    have wf'' : nfa''.val.WellFormed := by
      refine ih eq₂.symm ?_ (by simp [eq₁])
      apply pushNode_wf eq₁ wf
      simp [Node.inBounds]
      omega

    apply pushNode_wf eq₃ wf''
    simp [Node.inBounds]
    have := wf''.start_lt
    omega
  | alternate e₁ e₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ eq₂ eq₃ eq₄ eq₅ eq₆
    simp [eq₆]

    have wf₁ : nfa₁.val.WellFormed := ih₁ eq₁.symm wf next_lt
    have wf₂ : nfa₂.val.WellFormed := ih₂ eq₃.symm wf₁ (Nat.lt_trans next_lt nfa₁.property)

    apply pushNode_wf eq₅ wf₂
    simp [Node.inBounds]
    have := wf₁.start_lt
    have := wf₂.start_lt
    omega
  | concat e₁ e₂ ih₁ ih₂ =>
    apply pushRegex.concat eq
    intro nfa₂ nfa₁ property eq₁ eq₂ eq₃
    simp [eq₃]

    have wf₂ : nfa₂.val.WellFormed := ih₂ eq₁.symm wf next_lt
    exact ih₁ eq₂.symm wf₂ wf₂.start_lt
  | star e ih =>
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' property eq₁ eq₂ eq₃ eq₄ eq₅
    simp [eq₅]

    have wf_placeholder : placeholder.val.WellFormed := by
      apply pushNode_wf eq₁ wf
      simp [Node.inBounds]
    have wf_compiled : compiled.val.WellFormed :=
      ih eq₂.symm wf_placeholder placeholder.property

    simp [eq₄, WellFormed.iff, NFA.get_eq_nodes_get]
    refine ⟨?_, ?_⟩
    . simp [eq₃]
      exact Nat.lt_trans placeholder.property compiled.property
    . intro i
      simp [eq₃]
      rw [Array.get_set]
      . split
        next =>
          simp [Node.inBounds]
          exact ⟨wf_compiled.start_lt, Nat.lt_trans (Nat.lt_trans next_lt placeholder.property) compiled.property⟩
        next ne =>
          have (i : Nat) (h : i < compiled.val.nodes.size) : compiled.val.nodes[i].inBounds compiled.val.nodes.size := by
            have := wf_compiled.inBounds ⟨i, h⟩
            exact this
          apply this
      . have := i.isLt
        simp [eq₃] at this
        exact this

theorem compile_wf : (compile e).WellFormed := by
  simp [compile]
  apply pushRegex_wf rfl done_WellFormed (by simp [done])

end Regex.NFA
