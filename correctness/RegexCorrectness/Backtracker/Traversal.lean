import Regex.Strategy
import RegexCorrectness.Data.BoundedIterator
import RegexCorrectness.Backtracker.Basic
import RegexCorrectness.Backtracker.Path

set_option autoImplicit false

open Regex.Data (BoundedIterator)
open String (Iterator)

namespace Regex.Backtracker.captureNextAux

section

variable {σ nfa wf it startIdx maxIdx visited stack}

theorem mem_of_mem_visited {s i} (hmem : visited.get s i) :
  (captureNextAux σ nfa wf startIdx maxIdx visited stack).2.get s i := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startIdx maxIdx with
  | base visited => simp [captureNextAux_base, hmem]
  | visited visited update state it stack' mem ih => simp [captureNextAux_visited mem, ih hmem]
  | done visited update state it stack' mem hn => simp [captureNextAux_done mem hn, BitMatrix.get_set, hmem]
  | fail visited update state it stack' mem hn => simp [captureNextAux_fail mem hn, BitMatrix.get_set, hmem]
  | epsilon visited update state it stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | split visited update state it stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])

theorem mem_of_mem_top_stack {entry stack'} (hstack : entry :: stack' = stack) :
  (captureNextAux σ nfa wf startIdx maxIdx visited stack).2.get entry.state entry.it.index := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startIdx maxIdx with
  | base visited => simp at hstack
  | visited visited update state it stack' mem ih =>
    simp [captureNextAux_visited mem]
    simp at hstack
    exact mem_of_mem_visited (by simp [hstack, mem])
  | done visited update state it stack' mem hn =>
    simp [captureNextAux_done mem hn]
    simp at hstack
    simp [hstack, BitMatrix.get_set]
  | fail visited update state it stack' mem hn =>
    simp [captureNextAux_fail mem hn]
    simp at hstack
    simp [hstack, BitMatrix.get_set]
  | epsilon visited update state it stack'' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | split visited update state it stack'' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])

end

/-
Here, we consider a minimal invariant enough to prove the "soundness" of the backtracker; a capture group found by the backtracker indeed corresponds to a match by the regex.
Therefore, we are only concenred about that the states in the stack are reachable from the start node starting from a particular position.

NOTE: if we want to show that the backtracker is complete (i.e., if the regex matches a string, then the backtracker will find a capture group), we need new invariants
about the visited set so that we can reason about the case the backtracker returns `.none`.

Current candidates are:

1. Closure under transition: ∀ (state, pos) ∈ visited, nfa.Step 0 state pos state' pos' → (state', pos') ∈ visited ∨ ∃ entry ∈ stack, entry.state = state' ∧ entry.it.poss = pos'
  * At the end of the traversal, we can use this invariant to show that the visited set is a reflexive-transitive closure of the step relation.
2. Upper bound of the visited set: ∀ (state, pos) ∈ visited, (state, pos) ∈ visisted₀ ∨ ∃ it, Path nfa wf it₀ it state update
  * We'll strengthen `UpperInv` to give an upper bound of the visited set.
  * Combined with the closure property, we can show that the traversal adds just the states reachable from the starting node at a particular position.
3. The visited set doesn't contain the `.done` state.
  * This implies that if the traversal returns `.none`, then there is no match starting from the particular position.
-/
section

variable {nfa wf startIdx maxIdx visited stack update' visited'}

structure UpperInv (wf : nfa.WellFormed) (it₀ : Iterator) (stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)) where
  reachable : ∀ entry ∈ stack, Path nfa wf it₀ entry.it.it entry.state entry.update

theorem path_done_of_some {it₀} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stack = (.some update', visited'))
  (inv : UpperInv wf it₀ stack) :
  ∃ state it', nfa[state] = .done ∧ Path nfa wf it₀ it' state update' := by
  induction visited, stack using captureNextAux.induct' HistoryStrategy nfa wf startIdx with
  | base visited => simp [captureNextAux_base] at hres
  | visited visited update state it stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    have inv' : UpperInv wf it₀ stack' := by
      have reachable entry (mem : entry ∈ stack') : Path nfa wf it₀ entry.it.it entry.state entry.update :=
        inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | done visited update state it stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    have path := inv.reachable ⟨update, state, it⟩ (by simp)
    exact ⟨state, it.it, hn, hres.1 ▸ path⟩
  | fail visited update state it stack' mem hn => simp [captureNextAux_fail mem hn] at hres
  | epsilon visited update state it stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn] at hres
    have inv' : UpperInv wf it₀ (⟨update, state', it⟩ :: stack') := by
      have reachable entry (mem : entry ∈ ⟨update, state', it⟩ :: stack') : Path nfa wf it₀ entry.it.it entry.state entry.update := by
        simp at mem
        cases mem with
        | inl eq' =>
          simp [eq']
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          exact path.more (.epsilon (Nat.zero_le _) state.isLt hn path.validR) (by simp)
        | inr mem => exact inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | split visited update state it stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn] at hres
    let stack'' := ⟨update, state₁, it⟩ :: ⟨update, state₂, it⟩ :: stack'
    have inv' : UpperInv wf it₀ stack'' := by
      have reachable entry (mem : entry ∈ stack'') : Path nfa wf it₀ entry.it.it entry.state entry.update := by
        simp [stack''] at mem
        match mem with
        | .inl eq₁ =>
          simp [eq₁]
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          exact path.more (.splitLeft (Nat.zero_le _) state.isLt hn path.validR) (by simp)
        | .inr (.inl eq₂) =>
          simp [eq₂]
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          exact path.more (.splitRight (Nat.zero_le _) state.isLt hn path.validR) (by simp)
        | .inr (.inr mem) => exact inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn] at hres
    have inv' : UpperInv wf it₀ (⟨update', state', it⟩ :: stack') := by
      have reachable entry (mem : entry ∈ ⟨update', state', it⟩ :: stack') : Path nfa wf it₀ entry.it.it entry.state entry.update := by
        simp at mem
        cases mem with
        | inl eq' =>
          simp [eq']
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          exact path.more (.save (Nat.zero_le _) state.isLt hn path.validR) (by simp [update', HistoryStrategy, BoundedIterator.pos])
        | inr mem => exact inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht] at hres
    have inv' : UpperInv wf it₀ (⟨update, state', it⟩ :: stack') := by
      have reachable entry (mem : entry ∈ ⟨update, state', it⟩ :: stack') : Path nfa wf it₀ entry.it.it entry.state entry.update := by
        simp at mem
        cases mem with
        | inl eq' =>
          simp [eq']
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          exact path.more (.anchor (Nat.zero_le _) state.isLt hn path.validR ht) (by simp)
        | inr mem => exact inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht] at hres
    have inv' : UpperInv wf it₀ stack' := by
      have reachable entry (mem : entry ∈ stack') : Path nfa wf it₀ entry.it.it entry.state entry.update :=
        inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc] at hres
    have inv' : UpperInv wf it₀ (⟨update, state', it.next hnext⟩ :: stack') := by
      have reachable entry (mem : entry ∈ ⟨update, state', it.next hnext⟩ :: stack') : Path nfa wf it₀ entry.it.it entry.state entry.update := by
        simp at mem
        cases mem with
        | inl eq' =>
          simp [eq']
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          have v : it.Valid := it.valid_of_it_valid path.validR
          have ⟨l, r, vf⟩ := v.validFor_of_hasNext hnext
          exact path.more (.char (Nat.zero_le _) state.isLt hn (hc ▸ vf)) (by simp)
        | inr mem => exact inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc] at hres
    have inv' : UpperInv wf it₀ stack' := by
      have reachable entry (mem : entry ∈ stack') : Path nfa wf it₀ entry.it.it entry.state entry.update :=
        inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext] at hres
    have inv' : UpperInv wf it₀ stack' := by
      have reachable entry (mem : entry ∈ stack') : Path nfa wf it₀ entry.it.it entry.state entry.update :=
        inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc] at hres
    have inv' : UpperInv wf it₀ (⟨update, state', it.next hnext⟩ :: stack') := by
      have reachable entry (mem : entry ∈ ⟨update, state', it.next hnext⟩ :: stack') : Path nfa wf it₀ entry.it.it entry.state entry.update := by
        simp at mem
        cases mem with
        | inl eq' =>
          simp [eq']
          have path := inv.reachable ⟨update, state, it⟩ (by simp)
          simp at path
          have v : it.Valid := it.valid_of_it_valid path.validR
          have ⟨l, r, vf⟩ := v.validFor_of_hasNext hnext
          exact path.more (.sparse (Nat.zero_le _) state.isLt hn vf hc) (by simp)
        | inr mem => exact inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc] at hres
    have inv' : UpperInv wf it₀ stack' := by
      have reachable entry (mem : entry ∈ stack') : Path nfa wf it₀ entry.it.it entry.state entry.update :=
        inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext] at hres
    have inv' : UpperInv wf it₀ stack' := by
      have reachable entry (mem : entry ∈ stack') : Path nfa wf it₀ entry.it.it entry.state entry.update :=
        inv.reachable entry (by simp [mem])
      exact ⟨reachable⟩
    exact ih hres inv'

end

end Regex.Backtracker.captureNextAux
