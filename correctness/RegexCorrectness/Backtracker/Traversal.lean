import Regex.Strategy
import RegexCorrectness.Data.BoundedIterator
import RegexCorrectness.Backtracker.Basic
import RegexCorrectness.Backtracker.Path

set_option autoImplicit false

open Regex.Data (BitMatrix BoundedIterator)
open String (Pos Iterator)
open Regex.NFA (Step)

namespace Regex.Backtracker.captureNextAux

section

variable {σ nfa wf it startIdx maxIdx visited stack}

theorem mem_of_mem_visited {s i} (hmem : visited.get s i) :
  (captureNextAux σ nfa wf startIdx maxIdx visited stack).2.get s i := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startIdx maxIdx with
  | base visited => simp [captureNextAux_base, hmem]
  | visited visited update state it stack' mem ih => simp [captureNextAux_visited mem, ih hmem]
  | done visited update state it stack' mem hn => simp [captureNextAux_done mem hn, BitMatrix.get_set, hmem]
  | fail visited update state it stack' mem visited' hn ih =>
    rw [captureNextAux_fail mem hn]
    exact ih (by simp [visited', BitMatrix.get_set, hmem])
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
  | fail visited update state it stack' mem visited' hn ih =>
    rw [captureNextAux_fail mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [BitMatrix.get_set, hstack, mem])
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

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat}
{visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)} {update' visited'}

def StackInv (wf : nfa.WellFormed) (bit₀ : BoundedIterator startIdx maxIdx) (stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)) : Prop :=
  ∀ entry ∈ stack, Path nfa wf bit₀.it entry.it.it entry.state entry.update

namespace StackInv

theorem path {bit₀} {entry : StackEntry HistoryStrategy nfa startIdx maxIdx} {stack' : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}
  (inv : StackInv wf bit₀ (entry :: stack')) :
  Path nfa wf bit₀.it entry.it.it entry.state entry.update := inv entry (by simp)

theorem preserves {bit₀ entry stack'} (inv : StackInv wf bit₀ (entry :: stack')) (nextEntries) (hstack : stack = nextEntries ++ stack')
  (hnext : ∀ entry' ∈ nextEntries,
    ∃ update, nfa.Step 0 entry.state entry.it.it entry'.state entry'.it.it update ∧ entry'.update = List.append entry.update (List.ofOption update)) :
  StackInv wf bit₀ stack := by
  simp [hstack]
  intro entry' mem'
  simp at mem'
  cases mem' with
  | inl mem' =>
    have path := inv.path
    have ⟨update, step, hupdate⟩ := hnext entry' mem'
    exact path.more step hupdate
  | inr mem' => exact inv entry' (by simp [mem'])

end StackInv

theorem path_done_of_some {bit₀} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stack = (.some update', visited'))
  (inv : StackInv wf bit₀ stack) :
  ∃ state it', nfa[state] = .done ∧ Path nfa wf bit₀.it it' state update' := by
  induction visited, stack using captureNextAux.induct' HistoryStrategy nfa wf startIdx with
  | base visited => simp [captureNextAux_base] at hres
  | visited visited update state it stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'
  | done visited update state it stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    exact ⟨state, it.it, hn, hres.1 ▸ inv.path⟩
  | fail visited update state it stack' mem visited' hn ih =>
    rw [captureNextAux_fail mem hn] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'
  | epsilon visited update state it stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn] at hres
    have inv' : StackInv wf bit₀ (⟨update, state', it⟩ :: stack') := by
      apply inv.preserves [⟨update, state', it⟩] (by simp)
      simp
      exact ⟨.none, .epsilon (Nat.zero_le _) state.isLt hn inv.path.validR, by simp⟩
    exact ih hres inv'
  | split visited update state it stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn] at hres
    have inv' : StackInv wf bit₀ (⟨update, state₁, it⟩ :: ⟨update, state₂, it⟩ :: stack') := by
      apply inv.preserves [⟨update, state₁, it⟩, ⟨update, state₂, it⟩] (by simp)
      simp
      exact ⟨
        ⟨.none, .splitLeft (Nat.zero_le _) state.isLt hn inv.path.validR, by simp⟩,
        ⟨.none, .splitRight (Nat.zero_le _) state.isLt hn inv.path.validR, by simp⟩
      ⟩
    exact ih hres inv'
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn] at hres
    have inv' : StackInv wf bit₀ (⟨update', state', it⟩ :: stack') := by
      apply inv.preserves [⟨update', state', it⟩] (by simp)
      simp
      exact ⟨.some (offset, it.pos), .save (Nat.zero_le _) state.isLt hn inv.path.validR, by simp [update', HistoryStrategy]⟩
    exact ih hres inv'
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht] at hres
    have inv' : StackInv wf bit₀ (⟨update, state', it⟩ :: stack') := by
      apply inv.preserves [⟨update, state', it⟩] (by simp)
      simp
      exact ⟨.none, .anchor (Nat.zero_le _) state.isLt hn inv.path.validR ht, by simp⟩
    exact ih hres inv'
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc] at hres
    have inv' : StackInv wf bit₀ (⟨update, state', it.next hnext⟩ :: stack') := by
      apply inv.preserves [⟨update, state', it.next hnext⟩] (by simp)
      simp
      have ⟨l, r, vf⟩ := (it.valid_of_it_valid inv.path.validR).validFor_of_hasNext hnext
      exact ⟨.none, .char (Nat.zero_le _) state.isLt hn (hc ▸ vf), by simp⟩
    exact ih hres inv'
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc] at hres
    have inv' : StackInv wf bit₀ (⟨update, state', it.next hnext⟩ :: stack') := by
      apply inv.preserves [⟨update, state', it.next hnext⟩] (by simp)
      simp
      have ⟨l, r, vf⟩ := (it.valid_of_it_valid inv.path.validR).validFor_of_hasNext hnext
      exact ⟨.none, .sparse (Nat.zero_le _) state.isLt hn vf hc, by simp⟩
    exact ih hres inv'
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext] at hres
    have inv' : StackInv wf bit₀ stack' := inv.preserves [] (by simp) (by simp)
    exact ih hres inv'

end

section

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}

def StringInv (s : String) (stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)) : Prop :=
  ∀ entry ∈ stack, entry.it.toString = s

namespace StringInv

theorem drop {entry} (inv : StringInv s (entry :: stack)) : StringInv s stack :=
  fun entry' mem' => inv entry' (by simp [mem'])

theorem cons {entry} (inv : StringInv s stack) (h : entry.it.toString = s) : StringInv s (entry :: stack) := by
  intro entry' mem'
  simp at mem'
  cases mem' with
  | inl eq => rw [eq, h]
  | inr mem' => exact inv entry' mem'

theorem cons_iff {entry} : StringInv s (entry :: stack) ↔ entry.it.toString = s ∧ StringInv s stack := by
  apply Iff.intro
  . intro inv
    exact ⟨inv entry (by simp), inv.drop⟩
  . intro ⟨h, inv⟩
    exact inv.cons h

end StringInv

def ClosureInv (s : String) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bit : BoundedIterator startIdx maxIdx) (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx) (update : Option (Nat × Pos)),
    bit.toString = s →
    visited.get state bit.index →
    nfa.Step 0 state bit.it state' bit'.it update →
    visited.get state' bit'.index ∨ ∃ entry ∈ stack, entry.state = state' ∧ entry.it = bit'

namespace ClosureInv

-- Preservation of the non-visited cases
theorem preserves {entry stack'} (inv : ClosureInv s visited (entry :: stack)) (hstring : entry.it.toString = s)
  (nextEntries : List (StackEntry HistoryStrategy nfa startIdx maxIdx)) (hstack : stack' = nextEntries ++ stack)
  (hnext : ∀ (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx) (update : Option (Nat × Pos)),
    nfa.Step 0 entry.state entry.it.it state' bit'.it update →
    ∃ entry' ∈ nextEntries, entry'.state = state' ∧ entry'.it = bit') :
  ClosureInv s (visited.set entry.state entry.it.index) stack' := by
  intro state bit state' bit' update' eqs hmem step
  simp [visited.get_set] at hmem
  match hmem with
  | .inl ⟨eqstate, eqindex⟩ =>
    -- There is a step from the top entry. Use the given property to find the next entries in the next stack top.
    have eqit : entry.it = bit := by
      simp [BoundedIterator.ext_index_iff, eqindex, eqs, hstring]
    have ⟨entry', hmem', eqstate', eqit'⟩ := hnext state' bit' update' (eqit ▸ eqstate ▸ step)
    exact .inr ⟨entry', by simp [hstack, hmem'], eqstate', eqit'⟩
  | .inr hmem =>
    -- There is a step from the entry below the stack top.
    match inv state bit state' bit' update' eqs hmem step with
    | .inl hmem' => exact .inl (visited.get_set_of_get hmem')
    | .inr ⟨entry', hmem', eqstate, eqit⟩ =>
      simp at hmem'
      cases hmem' with
      | inl eq =>
        -- If the step moves to the top entry, then this iteration marks the entry as visited.
        simp [eq, ←eqstate, ←eqit, visited.get_set_eq]
      | inr hmem' =>
        -- If the step moves to the entry below the stack top, then the entry is still in the stack.
        exact .inr ⟨entry', by simp [hstack, hmem'], eqstate, eqit⟩

end ClosureInv

/--
When the backtracker returns `.none`, it explores all reachable states and thus the visited set satisfies the closure property under the step relation.
-/
theorem step_closure {s : String} {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stack = result)
  (isNone : result.1 = .none)
  (cinv : ClosureInv s visited stack) (sinv : StringInv s stack) :
  ClosureInv s result.2 [] := by
  induction visited, stack using captureNextAux.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | base visited =>
    simp [captureNextAux_base] at hres
    simp [←hres, cinv]
  | visited visited update state it stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    have cinv' : ClosureInv s visited stack' := by
      intro state₁ bit state₂ bit' update' eqs hmem step
      match cinv state₁ bit state₂ bit' update' eqs hmem step with
      | .inl hmem' => exact .inl hmem'
      | .inr ⟨entry, hmem', eqstate, eqit⟩ =>
        simp at hmem'
        cases hmem' with
        | inl eq => simp [eq, ←eqstate, ←eqit, mem]
        | inr hmem' => exact .inr ⟨entry, hmem', eqstate, eqit⟩
    exact ih hres cinv' sinv.drop
  | done visited update state it stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    simp [←hres] at isNone
  | fail visited update state it stack' mem visited' hn ih =>
    rw [captureNextAux_fail mem hn] at hres
    have cinv' : ClosureInv s visited' stack' := by
      apply cinv.preserves (sinv _ (by simp)) [] (by simp)
      intro state' bit' update' step
      rw [Step.iff_fail hn] at step
      exact step.elim
    exact ih hres cinv' sinv.drop
  | epsilon visited update state it stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn] at hres
    have cinv' : ClosureInv s visited' (⟨update, state', it⟩ :: stack') := by
      apply cinv.preserves (sinv _ (by simp)) [⟨update, state', it⟩] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_epsilon hn] at step
      have ⟨_, eqstate'', eqit'', _⟩ := step
      simp [Fin.eq_of_val_eq eqstate'', BoundedIterator.ext_iff, eqit'']
    have sinv' : StringInv s (⟨update, state', it⟩ :: stack') := by
      simp [StringInv.cons_iff, sinv.drop]
      exact sinv ⟨update, state, it⟩ (by simp)
    exact ih hres cinv' sinv'
  | split visited update state it stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn] at hres
    have cinv' : ClosureInv s visited' (⟨update, state₁, it⟩ :: ⟨update, state₂, it⟩ :: stack') := by
      apply cinv.preserves (sinv _ (by simp)) [⟨update, state₁, it⟩, ⟨update, state₂, it⟩] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_split hn] at step
      have ⟨_, eqstate'', eqit'', _⟩ := step
      simp [BoundedIterator.ext_iff, eqit'']
      cases eqstate'' with
      | inl eq₁ => simp [Fin.eq_of_val_eq eq₁]
      | inr eq₂ => simp [Fin.eq_of_val_eq eq₂]
    have sinv' : StringInv s (⟨update, state₁, it⟩ :: ⟨update, state₂, it⟩ :: stack') := by
      simp [StringInv.cons_iff, sinv.drop]
      exact sinv ⟨update, state, it⟩ (by simp)
    exact ih hres cinv' sinv'
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn] at hres
    have cinv' : ClosureInv s visited' (⟨update', state', it⟩ :: stack') := by
      apply cinv.preserves (sinv _ (by simp)) [⟨update', state', it⟩] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_save hn] at step
      have ⟨_, eqstate'', eqit'', _⟩ := step
      simp [Fin.eq_of_val_eq eqstate'', BoundedIterator.ext_iff, eqit'']
    have sinv' : StringInv s (⟨update', state', it⟩ :: stack') := by
      simp [StringInv.cons_iff, sinv.drop]
      exact sinv ⟨update, state, it⟩ (by simp)
    exact ih hres cinv' sinv'
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht] at hres
    have cinv' : ClosureInv s visited' (⟨update, state', it⟩ :: stack') := by
      apply cinv.preserves (sinv _ (by simp)) [⟨update, state', it⟩] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_anchor hn] at step
      have ⟨_, eqstate'', eqit'', _⟩ := step
      simp [Fin.eq_of_val_eq eqstate'', BoundedIterator.ext_iff, eqit'']
    have sinv' : StringInv s (⟨update, state', it⟩ :: stack') := by
      simp [StringInv.cons_iff, sinv.drop]
      exact sinv ⟨update, state, it⟩ (by simp)
    exact ih hres cinv' sinv'
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht] at hres
    have cinv' : ClosureInv s visited' stack' := by
      apply cinv.preserves (sinv _ (by simp)) [] (by simp)
      intro state'' bit'' update' step
      simp [Step.iff_anchor hn] at step
      simp [step] at ht
    exact ih hres cinv' sinv.drop
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc] at hres
    have cinv' : ClosureInv s visited' (⟨update, state', it.next hnext⟩ :: stack') := by
      apply cinv.preserves (sinv _ (by simp)) [⟨update, state', it.next hnext⟩] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_char hn] at step
      have ⟨l, r, _, eqstate'', eqit'', _, _⟩ := step
      simp [Fin.eq_of_val_eq eqstate'', BoundedIterator.ext_iff, eqit'', BoundedIterator.next, Iterator.next'_eq_next]
    have sinv' : StringInv s (⟨update, state', it.next hnext⟩ :: stack') := by
      simp [StringInv.cons_iff, BoundedIterator.next_toString, sinv.drop]
      exact sinv ⟨update, state, it⟩ (by simp)
    exact ih hres cinv' sinv'
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc] at hres
    have cinv' : ClosureInv s visited' stack' := by
      apply cinv.preserves (sinv _ (by simp)) [] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_char hn] at step
      have ⟨l, r, _, _, _, _, vf⟩ := step
      simp at vf
      simp [BoundedIterator.curr, Iterator.curr'_eq_curr, vf.curr] at hc
    exact ih hres cinv' sinv.drop
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext] at hres
    have cinv' : ClosureInv s visited' stack' := by
      apply cinv.preserves (sinv _ (by simp)) [] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_char hn] at step
      have ⟨l, r, _, _, _, _, vf⟩ := step
      simp at vf
      simp [BoundedIterator.hasNext, vf.hasNext] at hnext
    exact ih hres cinv' sinv.drop
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc] at hres
    have cinv' : ClosureInv s visited' (⟨update, state', it.next hnext⟩ :: stack') := by
      apply cinv.preserves (sinv _ (by simp)) [⟨update, state', it.next hnext⟩] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_sparse hn] at step
      have ⟨l, c, r, _, eqstate'', eqit'', _, vf, hc'⟩ := step
      simp [Fin.eq_of_val_eq eqstate'', BoundedIterator.ext_iff, eqit'', BoundedIterator.next, Iterator.next'_eq_next]
    have sinv' : StringInv s (⟨update, state', it.next hnext⟩ :: stack') := by
      simp [StringInv.cons_iff, BoundedIterator.next_toString, sinv.drop]
      exact sinv ⟨update, state, it⟩ (by simp)
    exact ih hres cinv' sinv'
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc] at hres
    have cinv' : ClosureInv s visited' stack' := by
      apply cinv.preserves (sinv _ (by simp)) [] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_sparse hn] at step
      have ⟨l, c, r, _, _, _, _, vf, hc'⟩ := step
      simp at vf
      simp [BoundedIterator.curr, Iterator.curr'_eq_curr, vf.curr] at hc
      exact (hc hc').elim
    exact ih hres cinv' sinv.drop
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext] at hres
    have cinv' : ClosureInv s visited' stack' := by
      apply cinv.preserves (sinv _ (by simp)) [] (by simp)
      intro state'' bit'' update' step
      rw [Step.iff_sparse hn] at step
      have ⟨l, c, r, _, _, _, _, vf, _⟩ := step
      simp at vf
      simp [BoundedIterator.hasNext, vf.hasNext] at hnext
    exact ih hres cinv' sinv.drop

def StepClosure (s : String) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bit : BoundedIterator startIdx maxIdx) (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx) (update : Option (Nat × Pos)),
    bit.toString = s →
    visited.get state bit.index →
    nfa.Step 0 state bit.it state' bit'.it update →
    visited.get state' bit'.index

def PathClosure (s : String) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bit : BoundedIterator startIdx maxIdx) (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx) (update : List (Nat × Pos)),
    bit.toString = s →
    visited.get state bit.index →
    nfa.Path 0 state bit.it state' bit'.it update →
    visited.get state' bit'.index

theorem PathClosure.of_step_closure {s} (wf : nfa.WellFormed) (h : StepClosure s visited) : PathClosure s visited := by
  let motive (i : Nat) (it : Iterator) : Prop :=
    ∃ (isLt : i < nfa.nodes.size) (bit : BoundedIterator startIdx maxIdx), bit.toString = s ∧ it = bit.it ∧ visited.get ⟨i, isLt⟩ bit.index
  have cls i it j it' update (base : motive i it) (step : nfa.Step 0 i it j it' update) : motive j it' := by
    have ⟨_, bit, eqs, eqit, hmem⟩ := base

    have ge' : startIdx ≤ it'.pos.byteIdx :=
      calc startIdx
        _ ≤ it.pos.byteIdx := eqit ▸ bit.ge
        _ ≤ it'.pos.byteIdx := step.le_pos
    have le' : it'.pos.byteIdx ≤ maxIdx :=
      calc it'.pos.byteIdx
        _ ≤ it.toString.endPos.byteIdx := step.le_endPos
        _ = maxIdx := eqit ▸ bit.eq.symm
    have eq' : maxIdx = it'.toString.endPos.byteIdx :=
      calc maxIdx
        _ = it.toString.endPos.byteIdx := eqit ▸ bit.eq
        _ = it'.toString.endPos.byteIdx := by rw [step.toString_eq]
    let bit' : BoundedIterator startIdx maxIdx := ⟨it', ge', le', eq'⟩

    have eqs' : bit'.toString = s := by
      simpa [bit', BoundedIterator.toString, ←eqs, ←eqit] using step.toString_eq
    have visited' := h ⟨i, step.lt⟩ bit ⟨j, step.lt_right wf⟩ bit' update eqs hmem (by simp [←eqit, bit', step])
    exact ⟨step.lt_right wf, bit', eqs', rfl, visited'⟩

  intro state bit state' bit' update eqs hmem path
  have ⟨isLt, _, eqs, eqit, hmem'⟩ := path.of_step_closure motive cls ⟨state.isLt, bit, eqs, rfl, hmem⟩
  exact (BoundedIterator.ext eqit) ▸ hmem'

/--
The closure property of the visited set can be lifted to paths.

Note: `nfa.Path` requires at least one step, so this is a transitive closure. However, the existence in the visited set
is obviously reflexive.
-/
theorem path_closure {s} {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stack = result)
  (isNone : result.1 = .none)
  (cinv : ClosureInv s visited stack) (sinv : StringInv s stack) :
  PathClosure s result.2 := by
  have cinv' : ClosureInv s result.2 [] := step_closure hres isNone cinv sinv
  have step_closure : StepClosure s result.2 := by
    intro state bit state' bit' update eqs hmem step
    have := cinv' state bit state' bit' update eqs hmem step
    simpa
  exact PathClosure.of_step_closure wf step_closure

end

section

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ : BoundedIterator startIdx maxIdx}
  {visited₀ visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}

def VisitedInv (wf : nfa.WellFormed) (bit₀ : BoundedIterator startIdx maxIdx) (visited₀ visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bit : BoundedIterator startIdx maxIdx),
    bit₀.toString = bit.toString →
    visited.get state bit.index →
    visited₀.get state bit₀.index ∨ ∃ update, Path nfa wf bit₀.it bit.it state update

theorem VisitedInv.preserves {bit : BoundedIterator startIdx maxIdx} {state : Fin nfa.nodes.size}
  (inv : VisitedInv wf bit₀ visited₀ visited)
  (eqs₀ : bit₀.toString = bit.toString)
  (update : List (Nat × Pos)) (path : Path nfa wf bit₀.it bit.it state update) :
  VisitedInv wf bit₀ visited₀ (visited.set state bit.index) := by
  intro state' bit' eqs hmem
  simp [visited.get_set] at hmem
  match hmem with
  | .inl ⟨eqstate, eqindex⟩ =>
    have eqit : bit' = bit := by
      simp [BoundedIterator.ext_index_iff, eqindex, ←eqs₀, ←eqs]
    simp [eqit, ←eqstate]
    exact .inr ⟨update, path⟩
  | .inr hmem =>
    have inv' := inv state' bit' eqs hmem
    simpa [visited.get_set] using inv'

theorem path_of_visited_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stack = result)
  (isNone : result.1 = .none)
  (vinv : VisitedInv wf bit₀ visited₀ visited) (sinv : StringInv bit₀.toString stack) (stinv : StackInv wf bit₀ stack) :
  VisitedInv wf bit₀ visited₀ result.2 := by
  induction visited, stack using captureNextAux.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | base visited =>
    simp [captureNextAux_base] at hres
    simp [←hres, vinv]
  | visited visited update state it stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    exact ih hres vinv sinv.drop (stinv.preserves [] (by simp) (by simp))
  | done visited update state it stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    simp [←hres] at isNone
  | fail visited update state it stack' mem visited' hn ih =>
    rw [captureNextAux_fail mem hn] at hres
    have := stinv.path
    have vinv' : VisitedInv wf bit₀ visited₀ visited' := vinv.preserves (sinv ⟨update, state, it⟩ (by simp)).symm update this
    sorry
  | epsilon visited update state it stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn] at hres
    sorry
  | split visited update state it stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn] at hres
    sorry
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn] at hres
    sorry
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht] at hres
    sorry
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht] at hres
    sorry
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc] at hres
    sorry
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc] at hres
    sorry
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext] at hres
    sorry
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc] at hres
    sorry
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc] at hres
    sorry
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext] at hres
    sorry

end

section

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}

def NotDoneInv (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bit : BoundedIterator startIdx maxIdx),
    visited.get state bit.index →
    nfa[state] ≠ .done

theorem NotDoneInv.preserves {state} {bit : BoundedIterator startIdx maxIdx} (inv : NotDoneInv visited)
  (h : nfa[state] ≠ .done):
  NotDoneInv (visited.set state bit.index) := by
  intro state' bit' hmem
  simp [visited.get_set] at hmem
  match hmem with
  | .inl ⟨eqstate, eqindex⟩ => simpa [←eqstate] using h
  | .inr hmem => exact inv state' bit' hmem

theorem not_done_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stack = result)
  (isNone : result.1 = .none)
  (inv : NotDoneInv visited) :
  NotDoneInv result.2 := by
  induction visited, stack using captureNextAux.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | base visited =>
    simp [captureNextAux_base] at hres
    simp [←hres, inv]
  | visited visited update state it stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    exact ih hres inv
  | done visited update state it stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    simp [←hres] at isNone
  | fail visited update state it stack' mem visited' hn ih =>
    rw [captureNextAux_fail mem hn] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | epsilon visited update state it stack' mem visited' state' hn ih =>
    rw [captureNextAux_epsilon mem hn] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | split visited update state it stack' mem visited' state₁ state₂ hn ih =>
    rw [captureNextAux_split mem hn] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | save visited update state it stack' mem visited' offset state' hn update' ih =>
    rw [captureNextAux_save mem hn] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | anchor_pos visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_pos mem hn ht] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | anchor_neg visited update state it stack' mem visited' a state' hn ht ih =>
    rw [captureNextAux_anchor_neg mem hn ht] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | char_pos visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_pos mem hn hnext hc] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | char_neg visited update state it stack' mem visited' c state' hn hnext hc ih =>
    rw [captureNextAux_char_neg mem hn hnext hc] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | char_end visited update state it stack' mem visited' c state' hn hnext ih =>
    rw [captureNextAux_char_end mem hn hnext] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | sparse_pos visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_pos mem hn hnext hc] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | sparse_neg visited update state it stack' mem visited' cs state' hn hnext hc ih =>
    rw [captureNextAux_sparse_neg mem hn hnext hc] at hres
    exact ih hres (inv.preserves (by simp [hn]))
  | sparse_end visited update state it stack' mem visited' cs state' hn hnext ih =>
    rw [captureNextAux_sparse_end mem hn hnext] at hres
    exact ih hres (inv.preserves (by simp [hn]))

end

end Regex.Backtracker.captureNextAux
