import Regex.Strategy
import RegexCorrectness.Data.BVPos
import RegexCorrectness.Backtracker.Basic
import RegexCorrectness.Backtracker.Path

set_option autoImplicit false

open Regex.Data (BitMatrix BVPos)
open String (ValidPos)
open Regex.NFA (Step)

namespace Regex.Backtracker.captureNextAux

section

variable {s : String} {σ : Strategy s} {nfa wf startPos pos visited stack}

theorem mem_of_mem_visited {s i} (hmem : visited.get s i) :
  (captureNextAux σ nfa wf startPos visited stack).2.get s i := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startPos with
  | base visited => simp [captureNextAux_base, hmem]
  | visited visited update state bvpos stack' mem ih => simp [captureNextAux_visited mem, ih hmem]
  | done visited update state bvpos stack' mem hn => simp [captureNextAux_done mem hn, BitMatrix.get_set, hmem]
  | next visited update state bvpos stack' mem hn ih =>
    rw [captureNextAux_next mem hn]
    exact ih (by simp [visited.get_set, hmem])

theorem mem_stack_top (entry stack') (hstack : entry :: stack' = stack) :
  (captureNextAux σ nfa wf startPos visited stack).2.get entry.state entry.pos.index := by
  induction visited, stack using captureNextAux.induct' σ nfa wf startPos with
  | base visited => simp at hstack
  | visited visited update state bvpos stack' mem =>
    simp [captureNextAux_visited mem]
    simp at hstack
    exact mem_of_mem_visited (by simp [hstack, mem])
  | done visited update state bvpos stack' mem hn =>
    simp [captureNextAux_done mem hn]
    simp at hstack
    simp [hstack, BitMatrix.get_set]
  | next visited update state bvpos stack' mem hn ih =>
    rw [captureNextAux_next mem hn]
    simp at hstack
    exact mem_of_mem_visited (by simp [visited.get_set, hstack])

end

section

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : ValidPos s}
  {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {stack : List (StackEntry (HistoryStrategy s) nfa startPos)} {update' visited'}

def StackInv (wf : nfa.WellFormed) (bvpos : BVPos startPos) (stack : List (StackEntry (HistoryStrategy s) nfa startPos)) : Prop :=
  ∀ entry ∈ stack, Path nfa wf bvpos.current entry.pos.current entry.state entry.update

namespace StackInv

theorem intro (bvpos : BVPos startPos) : StackInv wf bvpos [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] := by
  simp [StackInv, HistoryStrategy]
  exact .init

theorem path {bvpos : BVPos startPos} {entry : StackEntry (HistoryStrategy s) nfa startPos} {stack' : List (StackEntry (HistoryStrategy s) nfa startPos)}
  (inv : StackInv wf bvpos (entry :: stack')) :
  Path nfa wf bvpos.current entry.pos.current entry.state entry.update := inv entry (by simp)

theorem le {bvpos : BVPos startPos} {entry stack} (inv : StackInv wf bvpos (entry :: stack)) :
  bvpos ≤ entry.pos :=
  (inv entry (by simp)).le

theorem preserves' {bvpos entry stack'} (inv : StackInv wf bvpos (entry :: stack')) (nextEntries) (hstack : stack = nextEntries ++ stack')
  (hnext : ∀ entry' ∈ nextEntries,
    ∃ update, nfa.Step 0 entry.state entry.pos.current entry'.state entry'.pos.current update ∧ entry'.update = List.append entry.update (List.ofOption update)) :
  StackInv wf bvpos stack := by
  simp [hstack]
  intro entry' mem'
  simp at mem'
  cases mem' with
  | inl mem' =>
    have path := inv.path
    have ⟨update, step, hupdate⟩ := hnext entry' mem'
    exact path.more step hupdate
  | inr mem' => exact inv entry' (by simp [mem'])

theorem preserves {bvpos stack' update state pos} (inv : StackInv wf bvpos (⟨update, state, pos⟩ :: stack')) :
  StackInv wf bvpos (pushNext (HistoryStrategy s) nfa wf startPos stack' update state pos) := by
  cases stack', update, state, pos using pushNext.fun_cases' (HistoryStrategy s) nfa wf startPos with
  | done stack' update state pos hn =>
    rw [pushNext.done hn]
    exact inv.preserves' [] (by simp) (by simp)
  | fail stack' update state pos hn =>
    rw [pushNext.fail hn]
    exact inv.preserves' [] (by simp) (by simp)
  | epsilon stack' update state pos state' hn =>
    rw [pushNext.epsilon hn]
    apply inv.preserves' [⟨update, state', pos⟩] (by simp)
    simp
    exact ⟨.none, .epsilon (Nat.zero_le _) state.isLt hn, by simp⟩
  | split stack' update state pos state₁ state₂ hn =>
    rw [pushNext.split hn]
    apply inv.preserves' [⟨update, state₁, pos⟩, ⟨update, state₂, pos⟩] (by simp)
    simp
    exact ⟨
      ⟨.none, .splitLeft (Nat.zero_le _) state.isLt hn, by simp⟩,
      ⟨.none, .splitRight (Nat.zero_le _) state.isLt hn, by simp⟩
    ⟩
  | save stack' update state pos offset state' hn =>
    rw [pushNext.save hn]
    let update' := (HistoryStrategy s).write update offset pos.current
    apply inv.preserves' [⟨update', state', pos⟩] (by simp [update'])
    simp
    exact ⟨.some (offset, pos.current), .save (Nat.zero_le _) state.isLt hn, by simp [update']⟩
  | anchor_pos stack' update state pos a state' hn ht =>
    rw [pushNext.anchor_pos hn ht]
    apply inv.preserves' [⟨update, state', pos⟩] (by simp)
    simp
    exact ⟨.none, .anchor (Nat.zero_le _) state.isLt hn ht, by simp⟩
  | anchor_neg stack' update state pos a state' hn ht =>
    rw [pushNext.anchor_neg hn ht]
    apply inv.preserves' [] (by simp) (by simp)
  | char_pos stack' update state pos c state' hn ne hc =>
    rw [pushNext.char_pos hn ne hc]
    apply inv.preserves' [⟨update, state', pos.next ne⟩] (by simp)
    simp
    exact ⟨.none, .char (Nat.zero_le _) state.isLt hn (by simpa [BVPos.ext_iff] using ne) hc, by simp⟩
  | char_neg stack' update state pos c state' hn h =>
    rw [pushNext.char_neg hn h]
    apply inv.preserves' [] (by simp) (by simp)
  | sparse_pos stack' update state pos cs state' hn ne hc =>
    rw [pushNext.sparse_pos hn ne hc]
    apply inv.preserves' [⟨update, state', pos.next ne⟩] (by simp)
    simp
    exact ⟨.none, .sparse (Nat.zero_le _) state.isLt hn (by simpa [BVPos.ext_iff] using ne) hc, by simp⟩
  | sparse_neg stack' update state pos cs state' hn h =>
    rw [pushNext.sparse_neg hn h]
    apply inv.preserves' [] (by simp) (by simp)

end StackInv

theorem path_done_of_some {bvpos} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited stack = (.some update', visited'))
  (inv : StackInv wf bvpos stack) :
  ∃ (state : Fin nfa.nodes.size) (bvpos' : BVPos startPos),
    nfa[state] = .done ∧ bvpos ≤ bvpos' ∧ Path nfa wf bvpos.current bvpos'.current state update' := by
  induction visited, stack using captureNextAux.induct' (HistoryStrategy s) nfa wf startPos with
  | base visited => simp [captureNextAux_base] at hres
  | visited visited update state bvpos' stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    have inv' : StackInv wf bvpos stack' := inv.preserves' [] (by simp) (by simp)
    exact ih hres inv'
  | done visited update state bvpos' stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    exact ⟨state, bvpos', hn, inv.le, hres.1 ▸ inv.path⟩
  | next visited update state bvpos' stack' mem hn ih =>
    simp [captureNextAux_next mem hn] at hres
    exact ih hres inv.preserves

end

section

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : ValidPos s}
  {bvpos₀ : BVPos startPos} {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {stack : List (StackEntry (HistoryStrategy s) nfa startPos)}

def ClosureInv (bvpos₀ : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (stack : List (StackEntry (HistoryStrategy s) nfa startPos)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bvpos : BVPos startPos) (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos) (update : Option (Nat × ValidPos s)),
    bvpos₀ ≤ bvpos →
    visited.get state bvpos.index →
    nfa.Step 0 state bvpos.current state' bvpos'.current update →
    visited.get state' bvpos'.index ∨ ∃ entry ∈ stack, entry.state = state' ∧ entry.pos = bvpos'

namespace ClosureInv

-- Preservation of the non-visited cases
theorem preserves' {entry stack'} (inv : ClosureInv bvpos₀ visited (entry :: stack))
  (nextEntries : List (StackEntry (HistoryStrategy s) nfa startPos)) (hstack : stack' = nextEntries ++ stack)
  (hnext : ∀ (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos) (update : Option (Nat × ValidPos s)),
    nfa.Step 0 entry.state entry.pos.current state' bvpos'.current update →
    ∃ entry' ∈ nextEntries, entry'.state = state' ∧ entry'.pos = bvpos') :
  ClosureInv bvpos₀ (visited.set entry.state entry.pos.index) stack' := by
  intro state bvpos state' bvpos' update' le hmem step
  simp [visited.get_set] at hmem
  match hmem with
  | .inl ⟨eqstate, eqindex⟩ =>
    -- There is a step from the top entry. Use the given property to find the next entries in the next stack top.
    have eqpos : entry.pos = bvpos := BVPos.ext_index eqindex
    have ⟨entry', hmem', eqstate', eqpos'⟩ := hnext state' bvpos' update' (eqpos ▸ eqstate ▸ step)
    exact .inr ⟨entry', by simp [hstack, hmem'], eqstate', eqpos'⟩
  | .inr hmem =>
    -- There is a step from the entry below the stack top.
    match inv state bvpos state' bvpos' update' le hmem step with
    | .inl hmem' => exact .inl (visited.get_set_of_get hmem')
    | .inr ⟨entry', hmem', eqstate, eqpos⟩ =>
      simp at hmem'
      cases hmem' with
      | inl eq =>
        -- If the step moves to the top entry, then this iteration marks the entry as visited.
        simp [eq, ←eqstate, ←eqpos, visited.get_set_eq]
      | inr hmem' =>
        -- If the step moves to the entry below the stack top, then the entry is still in the stack.
        exact .inr ⟨entry', by simp [hstack, hmem'], eqstate, eqpos⟩

theorem preserves {stack update state bvpos} (wf : nfa.WellFormed) (inv : ClosureInv bvpos₀ visited (⟨update, state, bvpos⟩ :: stack)) (hdone : nfa[state] ≠ .done) :
  ClosureInv bvpos₀ (visited.set state bvpos.index) (pushNext (HistoryStrategy s) nfa wf startPos stack update state bvpos) := by
  cases stack, update, state, bvpos using pushNext.fun_cases' (HistoryStrategy s) nfa wf startPos with
  | done stack update state bvpos hn => simp [hn] at hdone
  | fail stack update state bvpos hn =>
    rw [pushNext.fail hn]
    apply inv.preserves' [] (by simp)
    simp [Step.iff_fail hn]
  | epsilon stack' update state bvpos state' hn =>
    rw [pushNext.epsilon hn]
    apply inv.preserves' [⟨update, state', bvpos⟩] (by simp)
    simp
    intro state'' bvpos'' update' step
    rw [Step.iff_epsilon hn] at step
    have ⟨_, eqstate'', eqbvpos'', _⟩ := step
    simp [Fin.eq_of_val_eq eqstate'', BVPos.ext_iff, eqbvpos'']
  | split stack' update state bvpos state₁ state₂ hn =>
    rw [pushNext.split hn]
    apply inv.preserves' [⟨update, state₁, bvpos⟩, ⟨update, state₂, bvpos⟩] (by simp)
    simp
    intro state'' bvpos'' update' step
    rw [Step.iff_split hn] at step
    have ⟨_, eqstate'', eqbvpos'', _⟩ := step
    simp [BVPos.ext_iff, eqbvpos'']
    cases eqstate'' with
    | inl eq₁ => simp [Fin.eq_of_val_eq eq₁]
    | inr eq₂ => simp [Fin.eq_of_val_eq eq₂]
  | save stack' update state bvpos offset state' hn =>
    rw [pushNext.save hn]
    let update' := (HistoryStrategy s).write update offset bvpos.current
    apply inv.preserves' [⟨update', state', bvpos⟩] (by simp [update'])
    simp
    intro state'' bvpos'' update' step
    rw [Step.iff_save hn] at step
    have ⟨_, eqstate'', eqbvpos'', _⟩ := step
    simp [Fin.eq_of_val_eq eqstate'', BVPos.ext_iff, eqbvpos'']
  | anchor_pos stack' update state bvpos a state' hn ht =>
    rw [pushNext.anchor_pos hn ht]
    apply inv.preserves' [⟨update, state', bvpos⟩] (by simp)
    simp
    intro state'' bvpos'' update' step
    rw [Step.iff_anchor hn] at step
    have ⟨_, eqstate'', eqbvpos'', _⟩ := step
    simp [Fin.eq_of_val_eq eqstate'', BVPos.ext_iff, eqbvpos'']
  | anchor_neg stack' update state bvpos a state' hn ht =>
    rw [pushNext.anchor_neg hn ht]
    apply inv.preserves' [] (by simp)
    simp [Step.iff_anchor hn, ht]
  | char_pos stack' update state bvpos c state' hn ne hc =>
    rw [pushNext.char_pos hn ne hc]
    apply inv.preserves' [⟨update, state', bvpos.next ne⟩] (by simp)
    simp
    intro state'' bvpos'' update' step
    rw [Step.iff_char hn] at step
    have ⟨_, _, eqstate'', eqbvpos'', _, _⟩ := step
    simp [Fin.eq_of_val_eq eqstate'', BVPos.ext_iff, eqbvpos'']
  | char_neg stack' update state bvpos c state' hn h =>
    rw [pushNext.char_neg hn h]
    apply inv.preserves' [] (by simp)
    have {ne : bvpos.current ≠ s.endValidPos} : bvpos.current.get ne ≠ c := by
      match h with
      | .inl eq => simp [eq] at ne
      | .inr ⟨ne', hc⟩ => simpa [BVPos.get] using hc
    simp [Step.iff_char hn, this]
  | sparse_pos stack' update state bvpos cs state' hn ne hc =>
    rw [pushNext.sparse_pos hn ne hc]
    apply inv.preserves' [⟨update, state', bvpos.next ne⟩] (by simp)
    simp
    intro state'' bvpos'' update' step
    rw [Step.iff_sparse hn] at step
    have ⟨_, _, eqstate'', eqbvpos'', _, hc'⟩ := step
    simp [Fin.eq_of_val_eq eqstate'', BVPos.ext_iff, eqbvpos'']
  | sparse_neg stack' update state bvpos cs state' hn h =>
    rw [pushNext.sparse_neg hn h]
    apply inv.preserves' [] (by simp)
    have {ne : bvpos.current ≠ s.endValidPos} : bvpos.current.get ne ∉ cs := by
      match h with
      | .inl eq => simp [eq] at ne
      | .inr ⟨ne', hc⟩ => simpa [BVPos.get] using hc
    simp [Step.iff_sparse hn, this]

end ClosureInv

/--
When the backtracker returns `.none`, it explores all reachable states and thus the visited set satisfies the closure property under the step relation.
-/
theorem step_closure {bvpos₀ bvpos : BVPos startPos} {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited stack = result)
  (isNone : result.1 = .none)
  (cinv : ClosureInv bvpos₀ visited stack) (stinv : StackInv wf bvpos stack) :
  ClosureInv bvpos₀ result.2 [] := by
  induction visited, stack using captureNextAux.induct' (HistoryStrategy s) nfa wf startPos with
  | base visited =>
    simp [captureNextAux_base] at hres
    simp [←hres, cinv]
  | visited visited update state bvpos stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    have cinv' : ClosureInv bvpos₀ visited stack' := by
      intro state₁ bvpos₁ state₂ bvpos₂ update' le hmem step
      match cinv state₁ bvpos₁ state₂ bvpos₂ update' le hmem step with
      | .inl hmem' => exact .inl hmem'
      | .inr ⟨entry, hmem', eqstate, eqit⟩ =>
        simp at hmem'
        cases hmem' with
        | inl eq => simp [eq, ←eqstate, ←eqit, mem]
        | inr hmem' => exact .inr ⟨entry, hmem', eqstate, eqit⟩
    exact ih hres cinv' (stinv.preserves' [] (by simp) (by simp))
  | done visited update state bvpos stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    simp [←hres] at isNone
  | next visited update state bvpos stack' mem hn ih =>
    simp [captureNextAux_next mem hn] at hres
    exact ih hres (cinv.preserves wf hn) stinv.preserves

def StepClosure (bvpos₀ : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bvpos : BVPos startPos) (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos) (update : Option (Nat × ValidPos s)),
    bvpos₀ ≤ bvpos →
    visited.get state bvpos.index →
    nfa.Step 0 state bvpos.current state' bvpos'.current update →
    visited.get state' bvpos'.index

def PathClosure (bvpos₀ : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bvpos : BVPos startPos) (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos) (update : List (Nat × ValidPos s)),
    bvpos₀ ≤ bvpos →
    visited.get state bvpos.index →
    nfa.Path 0 state bvpos.current state' bvpos'.current update →
    visited.get state' bvpos'.index

namespace PathClosure

theorem zero : PathClosure bvpos₀ (BitMatrix.zero nfa.nodes.size (startPos.remainingBytes + 1)) := by
  intro state bvpos state' bvpos' update reaches hmem path
  simp at hmem

theorem of_step_closure {bvpos₀ : BVPos startPos} (wf : nfa.WellFormed) (h : StepClosure bvpos₀ visited) : PathClosure bvpos₀ visited := by
  let motive (i : Nat) (pos : ValidPos s) : Prop :=
    ∃ (isLt : i < nfa.nodes.size) (bvpos : BVPos startPos), bvpos₀ ≤ bvpos ∧ pos = bvpos.current ∧ visited.get ⟨i, isLt⟩ bvpos.index
  have cls i pos j pos' update (base : motive i pos) (step : nfa.Step 0 i pos j pos' update) : motive j pos' := by
    have ⟨_, bvpos, le, hbvpos, hmem⟩ := base

    let bvpos' : BVPos startPos := ⟨pos', ValidPos.le_trans (hbvpos ▸ bvpos.le) step.le⟩

    have le₀' : bvpos₀ ≤ bvpos' := BVPos.le_trans le (BVPos.le_iff.mpr (hbvpos ▸ step.le))
    have visited' := h ⟨i, step.lt⟩ bvpos ⟨j, step.lt_right wf⟩ bvpos' update le hmem (by simp [←hbvpos, bvpos', step])
    exact ⟨step.lt_right wf, bvpos', le₀', rfl, visited'⟩

  intro state bvpos state' bvpos' update reaches hmem path
  have ⟨_, _, _, eqpos, hmem'⟩ := path.of_step_closure motive cls ⟨state.isLt, bvpos, reaches, rfl, hmem⟩
  exact (BVPos.ext eqpos) ▸ hmem'

end PathClosure

/--
The closure property of the visited set can be lifted to paths.

Note: `nfa.Path` requires at least one step, so this is a transitive closure. However, the existence in the visited set
is obviously reflexive.
-/
theorem path_closure {bvpos₀ bvpos : BVPos startPos} {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited stack = result)
  (isNone : result.1 = .none)
  (cinv : ClosureInv bvpos₀ visited stack) (stinv : StackInv wf bvpos stack) :
  PathClosure bvpos₀ result.2 := by
  have cinv' : ClosureInv bvpos₀ result.2 [] := step_closure hres isNone cinv stinv
  have step_closure : StepClosure bvpos₀ result.2 := by
    intro state bvpos state' bvpos' update le hmem step
    have := cinv' state bvpos state' bvpos' update le hmem step
    simpa
  exact PathClosure.of_step_closure wf step_closure

end

section

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : ValidPos s} {bvpos₀ bvpos : BVPos startPos}
  {visited visited' : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {stack : List (StackEntry (HistoryStrategy s) nfa startPos)}

def VisitedInv (wf : nfa.WellFormed) (bvpos₀ bvpos : BVPos startPos) (visited visited' : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) : Prop :=
  ∀ (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos),
    bvpos₀ ≤ bvpos' →
    visited'.get state' bvpos'.index →
    visited.get state' bvpos'.index ∨ ∃ update, Path nfa wf bvpos.current bvpos'.current state' update

namespace VisitedInv

theorem rfl (wf : nfa.WellFormed) (bvpos₀ bvpos : BVPos startPos) : VisitedInv wf bvpos₀ bvpos visited visited := by
  intro state bvpos _ hmem
  exact .inl hmem

theorem preserves {bvpos' : BVPos startPos} {state : Fin nfa.nodes.size}
  (inv : VisitedInv wf bvpos₀ bvpos visited visited')
  (update : List (Nat × ValidPos s)) (path : Path nfa wf bvpos.current bvpos'.current state update) :
  VisitedInv wf bvpos₀ bvpos visited (visited'.set state bvpos'.index) := by
  intro state' bvpos'' le' hmem
  simp [visited'.get_set] at hmem
  match hmem with
  | .inl ⟨eqstate, eqindex⟩ =>
    have eqbvpos : bvpos'' = bvpos' := BVPos.ext_index eqindex.symm
    exact .inr ⟨update, by simpa [eqbvpos, ←eqstate] using path⟩
  | .inr hmem =>
    have inv' := inv state' bvpos'' le' hmem
    simpa [visited'.get_set] using inv'

end VisitedInv

theorem visited_inv_of_none {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited' stack = result)
  (isNone : result.1 = .none)
  (vinv : VisitedInv wf bvpos₀ bvpos visited visited') (stinv : StackInv wf bvpos stack) :
  VisitedInv wf bvpos₀ bvpos visited result.2 := by
  induction visited', stack using captureNextAux.induct' (HistoryStrategy s) nfa wf startPos with
  | base visited =>
    simp [captureNextAux_base] at hres
    simp [←hres, vinv]
  | visited visited update state bvpos stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    exact ih hres vinv (stinv.preserves' [] (by simp) (by simp))
  | done visited update state bvpos stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    simp [←hres] at isNone
  | next visited update state bvpos stack' mem hn ih =>
    simp [captureNextAux_next mem hn] at hres
    have path := stinv ⟨update, state, bvpos⟩ (by simp)
    exact ih hres (vinv.preserves update path) stinv.preserves

end

section

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : ValidPos s} {bvpos₀ bvpos : BVPos startPos} {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {stack : List (StackEntry (HistoryStrategy s) nfa startPos)}

def NotDoneInv (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) : Prop :=
  ∀ (state : Fin nfa.nodes.size) (bvpos : BVPos startPos),
    visited.get state bvpos.index →
    nfa[state] ≠ .done

namespace NotDoneInv

theorem zero : NotDoneInv (BitMatrix.zero nfa.nodes.size (startPos.remainingBytes + 1)) := by
  intro state bvpos hmem
  simp at hmem

theorem preserves {state} {bvpos : BVPos startPos} (inv : NotDoneInv visited)
  (h : nfa[state] ≠ .done):
  NotDoneInv (visited.set state bvpos.index) := by
  intro state' bvpos' hmem
  simp [visited.get_set] at hmem
  match hmem with
  | .inl ⟨eqstate, eqindex⟩ => simpa [←eqstate] using h
  | .inr hmem => exact inv state' bvpos' hmem

end NotDoneInv

theorem not_done_of_none {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited stack = result)
  (isNone : result.1 = .none)
  (inv : NotDoneInv visited) :
  NotDoneInv result.2 := by
  induction visited, stack using captureNextAux.induct' (HistoryStrategy s) nfa wf startPos with
  | base visited =>
    simp [captureNextAux_base] at hres
    simp [←hres, inv]
  | visited visited update state bvpos stack' mem ih =>
    simp [captureNextAux_visited mem] at hres
    exact ih hres inv
  | done visited update state bvpos stack' mem hn =>
    simp [captureNextAux_done mem hn] at hres
    simp [←hres] at isNone
  | next visited update state bvpos stack' mem hn ih =>
    simp [captureNextAux_next mem hn] at hres
    exact ih hres (inv.preserves hn)

end

end Regex.Backtracker.captureNextAux
