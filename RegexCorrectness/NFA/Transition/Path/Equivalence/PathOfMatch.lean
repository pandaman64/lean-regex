-- When the regex matches a string, the compiled NFA accepts it.
import RegexCorrectness.Semantics.Expr.Matches
import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Transition.Path.Basic

import Mathlib.Tactic.Common

namespace Regex.NFA

theorem pathIn_of_matches.group {cs : List Char}
  (eq : pushRegex nfa next (.group i r) = nfa')
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next r = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs) :
  pathIn' nfa' nfa.nodes.size nfa'.val.start next cs := by
  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property _ _ eq₁ eq₂ eq₃ eq
  rw [eq]
  simp
  have path₃ : pathIn' nfa' nfa.nodes.size nfa'.val.start next [] := by
    have h₁ : nfa.nodes.size ≤ nfa'.val.start.val := by
      rw [eq₁]
      simp
    refine .last (.εStep h₁ nfa'.val.start.isLt ?_)
    rw [eq₁]
    simp [Node.εStep]
  have path₃ : pathIn' nfa'' nfa.nodes.size nfa'.val.start next [] := by
    apply path₃.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa''.property
    rw [pushRegex_get_lt eq₂.symm _ h₂]
  have path₂ : pathIn' nfa'' nfa'.val.nodes.size nfa''.val.start nfa'.val.start cs :=
    ih eq₂.symm
  have path₂₃ : pathIn' nfa'' nfa.nodes.size nfa''.val.start next (cs ++ []) :=
    pathIn'.trans (path₂.castBound (Nat.le_of_lt nfa'.property)) path₃
  simp at path₂₃
  have path₂₃ : pathIn' nfa''' nfa.nodes.size nfa''.val.start next cs := by
    apply path₂₃.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa'''.property
    rw [eq₃, pushNode_get_lt _ h₂]
  have path₁ : pathIn' nfa''' nfa.nodes.size nfa'''.val.start nfa''.val.start [] := by
    have h₁ : nfa.nodes.size ≤ nfa'''.val.start.val := by
      rw [eq₃]
      simp
      exact Nat.le_of_lt (Nat.lt_trans nfa'.property nfa''.property)
    refine .last (.εStep h₁ nfa'''.val.start.isLt ?_)
    rw [eq₃]
    simp [Node.εStep]
  exact path₁.trans path₂₃

theorem pathIn_of_matches.alternateLeft {cs : List Char}
  (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next r₁ = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs) :
  pathIn' nfa' nfa.nodes.size nfa'.val.start next cs := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ eq₂ eq₃ _ eq₅ eq
  rw [eq]
  simp
  have : pathIn' nfa₁ nfa.nodes.size nfa₁.val.start next cs := ih eq₁.symm
  have : pathIn' nfa' nfa.nodes.size nfa₁.val.start next cs := by
    apply this.cast
    intro i _ h₂
    have lt₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h₂ nfa₂.property
    have : i < nfa'.val.nodes.size := Nat.lt_trans lt₂ nfa'.property
    exists this
    simp [eq₅]
    rw [pushNode_get_lt _ lt₂]
    rw [pushRegex_get_lt eq₃.symm _ h₂]
  have : pathIn' nfa' nfa.nodes.size nfa'.val.start next ([] ++ cs) := by
    refine .more (.εStep ?_ nfa'.val.start.isLt ?_) this
    . rw [eq₅]
      simp
      exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
    . rw [eq₅]
      simp [Node.εStep, eq₂]
  simp at this
  exact this

theorem pathIn_of_matches.alternateRight {cs : List Char}
  (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next r₂ = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs) :
  pathIn' nfa' nfa.nodes.size nfa'.val.start next cs := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property _ _ eq₃ eq₄ eq₅ eq
  rw [eq]
  simp
  have : pathIn' nfa₂ nfa.nodes.size nfa₂.val.start next cs :=
    (ih eq₃.symm).castBound (Nat.le_of_lt nfa₁.property)
  have : pathIn' nfa' nfa.nodes.size nfa₂.val.start next cs := by
    apply this.cast
    intro i _ h₂
    have : i < nfa'.val.nodes.size := Nat.lt_trans h₂ nfa'.property
    exists this
    simp [eq₅]
    rw [pushNode_get_lt _ h₂]
  have : pathIn' nfa' nfa.nodes.size nfa'.val.start next ([] ++ cs) := by
    refine .more (.εStep ?_ nfa'.val.start.isLt ?_) this
    . rw [eq₅]
      simp
      exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
    . rw [eq₅]
      simp [Node.εStep, eq₄]
  simp at this
  exact this

theorem pathIn_of_matches.concat {cs₁ cs₂ : List Char}
  (eq : pushRegex nfa next (.concat r₁ r₂) = nfa')
  (ih₁ : ∀ {nfa next nfa'}, pushRegex nfa next r₁ = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs₁)
  (ih₂ : ∀ {nfa next nfa'}, pushRegex nfa next r₂ = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs₂) :
  pathIn' nfa' nfa.nodes.size nfa'.val.start next (cs₁ ++ cs₂) := by
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq
  rw [eq]
  simp
  have ih₁ : pathIn' nfa₁ nfa.nodes.size nfa₁.val.start nfa₂.val.start cs₁ :=
    (ih₁ eq₁.symm).castBound (Nat.le_of_lt nfa₂.property)
  have ih₂ : pathIn' nfa₂ nfa.nodes.size nfa₂.val.start next cs₂ := ih₂ eq₂.symm
  have ih₂ : pathIn' nfa₁ nfa.nodes.size nfa₂.val.start next cs₂ := by
    apply ih₂.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa₁.property
    rw [pushRegex_get_lt eq₁.symm _ h₂]
  exact ih₁.trans ih₂

theorem pathIn_of_matches.starConcat {cs₁ cs₂ : List Char}
  (eq : pushRegex nfa next (.star r) = nfa')
  (ih₁ : ∀ {nfa next nfa'}, pushRegex nfa next r = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs₁)
  (ih₂ : ∀ {nfa next nfa'}, pushRegex nfa next (.star r) = nfa' →
    pathIn' nfa' nfa.nodes.size nfa'.val.start next cs₂) :
  pathIn' nfa' nfa.nodes.size nfa'.val.start next (cs₁ ++ cs₂) := by
  have ih₂ : pathIn' nfa' nfa.nodes.size nfa'.val.start next cs₂ := ih₂ eq
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq
  rw [eq]
  simp
  rw [eq] at ih₂
  simp at ih₂
  have eqStart : nfa'.start = nfa.nodes.size := by
    rw [eq₄]
  have ih₁ : pathIn' compiled placeholder.val.nodes.size compiled.val.start nfa.nodes.size cs₁ :=
    ih₁ eq₂.symm
  have ih₁ : pathIn' nfa' placeholder.val.nodes.size compiled.val.start nfa.nodes.size cs₁ := by
    apply ih₁.cast
    intro i h₁ h₂
    rw [eq₄]
    simp [eq₃]
    exists h₂
    simp [get_eq_nodes_get, eq₃]
    rw [Array.get_set_ne (hj := h₂)]
    simp
    apply Nat.ne_of_lt (Nat.lt_of_lt_of_le placeholder.property h₁)
  have ih₁ : pathIn' nfa' nfa.nodes.size compiled.val.start nfa.nodes.size cs₁ :=
    ih₁.castBound (Nat.le_of_lt placeholder.property)
  have ih₂ : pathIn' nfa' nfa.nodes.size nfa.nodes.size next cs₂ := by
    rw [eqStart] at ih₂
    exact ih₂
  have := ih₁.trans ih₂
  have : pathIn' nfa' nfa.nodes.size nfa'.start next ([] ++ (cs₁ ++ cs₂)) := by
    refine .more (.εStep (by simp [eqStart]) nfa'.start.isLt ?_) this
    rw [eq₄]
    simp [get_eq_nodes_get, eq₃, Node.εStep]
  simp at this
  exact this

theorem pathIn_of_matches (eq : pushRegex nfa next r = nfa')
  (m : r.matches cs) :
  pathIn' nfa' nfa.nodes.size nfa'.val.start next cs := by
  induction m generalizing nfa next with
  | char c =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine .last (.charStep this nfa'.val.start.isLt ?_)
    rw [←eq]
    simp [pushRegex, Node.charStep]
  | sparse cls c hmem =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine .last (.charStep this nfa'.val.start.isLt ?_)
    rw [←eq]
    simp [pushRegex, Node.charStep, hmem]
  | epsilon =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine .last (.εStep this nfa'.val.start.isLt ?_)
    rw [←eq]
    simp [pushRegex, Node.εStep]
  | group _ ih => exact pathIn_of_matches.group eq ih
  | alternateLeft _ ih => exact pathIn_of_matches.alternateLeft eq ih
  | alternateRight _ ih => exact pathIn_of_matches.alternateRight eq ih
  | concat cs₁ cs₂ r₁ r₂ _ _ ih₁ ih₂ => exact pathIn_of_matches.concat eq ih₁ ih₂
  | starEpsilon =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine .last (.εStep this nfa'.val.start.isLt ?_)

    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      _ _ eq₃ eq₄ eq

    rw[eq]
    have : nfa'.start.val = nfa.nodes.size := by
      rw [eq₄]
    simp [this, eq₄, get_eq_nodes_get, eq₃, Node.εStep]
  | starConcat cs₁ cs₂ r _ _ ih₁ ih₂ => exact pathIn_of_matches.starConcat eq ih₁ ih₂

theorem pathIn_of_compile_matches (eq : compile r = nfa)
  (m : r.matches cs) :
  pathIn' nfa 1 nfa.start.val 0 cs := by
  unfold NFA.compile at eq
  set result := NFA.done.pushRegex ⟨0, by decide⟩ r with h
  have := pathIn_of_matches h.symm m
  rw [eq] at this
  exact this

end Regex.NFA
