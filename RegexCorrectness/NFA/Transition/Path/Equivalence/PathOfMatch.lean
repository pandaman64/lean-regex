-- When the regex matches a string, the compiled NFA accepts it.
import RegexCorrectness.Semantics.Expr.Matches
import RegexCorrectness.NFA.Basic
import RegexCorrectness.NFA.Compile
import RegexCorrectness.NFA.Transition.Path.Basic

import Mathlib.Tactic.Common

namespace Regex.NFA

theorem pathToNext_of_matches.group {cs : List Char}
  (eq : pushRegex nfa next (.group i r) = nfa')
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next r = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start cs := by
  apply pushRegex.group eq
  intro nfa' nfa'' nfa''' property _ _ eq₁ eq₂ eq₃ eq
  rw [eq]
  simp
  have path₃ : pathToNext nfa' next nfa.nodes.size nfa'.val.start [] := by
    have h₁ : nfa.nodes.size ≤ nfa'.val.start.val := by
      rw [eq₁]
      simp
    refine ⟨nfa'.val.start.val, [], [], rfl, .base h₁, ?_⟩
    refine .εStep h₁ nfa'.val.start.isLt ?_
    rw [eq₁]
    simp [Node.εStep]
  have path₃ : pathToNext nfa'' next nfa.nodes.size nfa'.val.start [] := by
    apply path₃.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa''.property
    rw [pushRegex_get_lt eq₂.symm _ h₂]
  have path₂ : pathToNext nfa'' nfa'.val.start nfa'.val.nodes.size nfa''.val.start cs :=
    ih eq₂.symm
  have path₂ : pathToNext nfa'' nfa'.val.start nfa.nodes.size nfa''.val.start cs :=
    path₂.castStart (Nat.le_of_lt nfa'.property)
  have path₂₃ : pathToNext nfa'' next nfa.nodes.size nfa''.val.start (cs ++ []) :=
    pathToNext.trans path₂ path₃
  simp at path₂₃
  have path₂₃ : pathToNext nfa''' next nfa.nodes.size nfa''.val.start cs := by
    apply path₂₃.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa'''.property
    rw [eq₃, pushNode_get_lt _ h₂]
  have path₁ : pathToNext nfa''' nfa''.val.start nfa''.val.nodes.size nfa'''.val.start [] := by
    have h₁ : nfa''.val.nodes.size ≤ nfa'''.val.start.val := by
      rw [eq₃]
      simp
    refine ⟨nfa'''.val.start, [], [], rfl, .base h₁, ?_⟩
    refine .εStep h₁ nfa'''.val.start.isLt ?_
    rw [eq₃]
    simp [Node.εStep]
  have path₁ : pathToNext nfa''' nfa''.val.start nfa.nodes.size nfa'''.val.start [] := by
    apply path₁.castStart (Nat.le_of_lt ?_)
    exact Nat.lt_trans nfa'.property nfa''.property
  exact pathToNext.trans path₁ path₂₃

theorem pathToNext_of_matches.alternateLeft {cs : List Char}
  (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next r₁ = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start cs := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ eq₂ eq₃ _ eq₅ eq
  rw [eq]
  simp
  have : pathToNext nfa₁ next nfa.nodes.size nfa₁.val.start cs := ih eq₁.symm
  have : pathToNext nfa' next nfa.nodes.size nfa₁.val.start cs := by
    apply this.cast
    intro i _ h₂
    have lt₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h₂ nfa₂.property
    have : i < nfa'.val.nodes.size := Nat.lt_trans lt₂ nfa'.property
    exists this
    simp [eq₅]
    rw [pushNode_get_lt _ lt₂]
    rw [pushRegex_get_lt eq₃.symm _ h₂]
  apply this.cons (.εStep ?_ nfa'.val.start.isLt ?_)
  . rw [eq₅]
    simp
    exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
  . rw [eq₅]
    simp [Node.εStep, eq₂]

theorem pathToNext_of_matches.alternateRight {cs : List Char}
  (eq : pushRegex nfa next (.alternate r₁ r₂) = nfa')
  (ih : ∀ {nfa next nfa'}, pushRegex nfa next r₂ = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start cs := by
  apply pushRegex.alternate eq
  intro nfa₁ start₁ nfa₂ start₂ _ nfa' property _ _ eq₃ eq₄ eq₅ eq
  rw [eq]
  simp
  have : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start cs :=
    (ih eq₃.symm).castStart (Nat.le_of_lt nfa₁.property)
  have : pathToNext nfa' next nfa.nodes.size nfa₂.val.start cs := by
    apply this.cast
    intro i _ h₂
    have : i < nfa'.val.nodes.size := Nat.lt_trans h₂ nfa'.property
    exists this
    simp [eq₅]
    rw [pushNode_get_lt _ h₂]
  apply this.cons (.εStep ?_ nfa'.val.start.isLt ?_)
  . rw [eq₅]
    simp
    exact Nat.le_of_lt (Nat.lt_trans nfa₁.property nfa₂.property)
  . rw [eq₅]
    simp [Node.εStep, eq₄]

theorem pathToNext_of_matches.concat {cs₁ cs₂ : List Char}
  (eq : pushRegex nfa next (.concat r₁ r₂) = nfa')
  (ih₁ : ∀ {nfa next nfa'}, pushRegex nfa next r₁ = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs₁)
  (ih₂ : ∀ {nfa next nfa'}, pushRegex nfa next r₂ = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs₂) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start (cs₁ ++ cs₂) := by
  apply pushRegex.concat eq
  intro nfa₂ nfa₁ property eq₂ eq₁ eq
  rw [eq]
  simp
  have ih₁ : pathToNext nfa₁ nfa₂.val.start nfa.nodes.size nfa₁.val.start cs₁ :=
    (ih₁ eq₁.symm).castStart (Nat.le_of_lt nfa₂.property)
  have ih₂ : pathToNext nfa₂ next nfa.nodes.size nfa₂.val.start cs₂ := ih₂ eq₂.symm
  have ih₂ : pathToNext nfa₁ next nfa.nodes.size nfa₂.val.start cs₂ := by
    apply ih₂.cast
    intro i _ h₂
    exists Nat.lt_trans h₂ nfa₁.property
    rw [pushRegex_get_lt eq₁.symm _ h₂]
  exact ih₁.trans ih₂

theorem pathToNext_of_matches.starConcat {cs₁ cs₂ : List Char}
  (eq : pushRegex nfa next (.star r) = nfa')
  (ih₁ : ∀ {nfa next nfa'}, pushRegex nfa next r = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs₁)
  (ih₂ : ∀ {nfa next nfa'}, pushRegex nfa next (.star r) = nfa' →
    pathToNext nfa' next nfa.nodes.size nfa'.val.start cs₂) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start (cs₁ ++ cs₂) := by
  have ih₂ : pathToNext nfa' next nfa.nodes.size nfa'.val.start cs₂ := ih₂ eq
  apply pushRegex.star eq
  intro placeholder compiled patched nfa' isLt inBounds property
    eq₁ eq₂ eq₃ eq₄ eq
  rw [eq]
  simp
  rw [eq] at ih₂
  simp at ih₂
  have eqStart : nfa'.start = nfa.nodes.size := by
    rw [eq₄]
  have ih₁ : pathToNext compiled nfa.nodes.size placeholder.val.nodes.size compiled.val.start cs₁ :=
    ih₁ eq₂.symm
  have ih₁ : pathToNext nfa' nfa.nodes.size placeholder.val.nodes.size compiled.val.start cs₁ := by
    apply ih₁.cast
    intro i h₁ h₂
    rw [eq₄]
    simp [eq₃]
    exists h₂
    simp [get_eq_nodes_get, eq₃]
    rw [Array.get_set_ne (hj := h₂)]
    simp
    apply Nat.ne_of_lt (Nat.lt_of_lt_of_le placeholder.property h₁)
  have ih₁ : pathToNext nfa' nfa.nodes.size nfa.nodes.size compiled.val.start cs₁ :=
    ih₁.castStart (Nat.le_of_lt placeholder.property)
  have ih₂ : pathToNext nfa' next nfa.nodes.size nfa.nodes.size cs₂ := by
    rw [eqStart] at ih₂
    exact ih₂
  have := ih₁.trans ih₂
  apply this.cons (.εStep (by simp [eqStart]) nfa'.start.isLt ?_)
  rw [eq₄]
  simp [get_eq_nodes_get, eq₃, Node.εStep]

theorem pathToNext_of_matches (eq : pushRegex nfa next r = nfa')
  (m : r.matches cs) :
  pathToNext nfa' next nfa.nodes.size nfa'.val.start cs := by
  induction m generalizing nfa next with
  | sparse cls c hmem =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨
      nfa'.val.start,
      [],
      [c],
      rfl,
      .base this,
      .charStep this nfa'.val.start.isLt ?_
    ⟩
    rw [←eq]
    simp [pushRegex, Node.charStep, hmem]
  | char c =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨
      nfa'.val.start,
      [],
      [c],
      rfl,
      .base this,
      .charStep this nfa'.val.start.isLt ?_
    ⟩
    rw [←eq]
    simp [pushRegex, Node.charStep]
  | epsilon =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨nfa'.val.start, [], [], rfl, .base this, .εStep this nfa'.val.start.isLt ?_⟩
    rw [←eq]
    simp [pushRegex, Node.εStep]
  | group _ ih => exact pathToNext_of_matches.group eq ih
  | alternateLeft _ ih => exact pathToNext_of_matches.alternateLeft eq ih
  | alternateRight _ ih => exact pathToNext_of_matches.alternateRight eq ih
  | concat cs₁ cs₂ r₁ r₂ _ _ ih₁ ih₂ => exact pathToNext_of_matches.concat eq ih₁ ih₂
  | starEpsilon =>
    have : nfa.nodes.size ≤ nfa'.val.start.val := ge_pushRegex_start eq
    refine ⟨nfa'.val.start, [], [], rfl, .base this, .εStep this nfa'.val.start.isLt ?_⟩

    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      _ _ eq₃ eq₄ eq

    rw[eq]
    have : nfa'.start.val = nfa.nodes.size := by
      rw [eq₄]
    simp [this, eq₄, get_eq_nodes_get, eq₃, Node.εStep]
  | starConcat cs₁ cs₂ r _ _ ih₁ ih₂ => exact pathToNext_of_matches.starConcat eq ih₁ ih₂

theorem pathToNext_of_compile_matches (eq : compile r = nfa)
  (m : r.matches cs) :
  pathToNext nfa 0 1 nfa.start cs := by
  unfold NFA.compile at eq
  set result := NFA.done.pushRegex ⟨0, by decide⟩ r with h
  have := pathToNext_of_matches h.symm m
  rw [eq] at this
  exact this

end Regex.NFA
