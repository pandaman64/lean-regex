import Regex.Data.SparseSet
import Regex.VM
import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.NFA

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) : Iterator → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | init {it i update} (cls : nfa.εClosure' it ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf it i update
  | more {i j k it update₁ update₂} (prev : VMPath nfa wf it i update₁) (step : nfa.CharStep it i j) (cls : nfa.εClosure' it.next j k update₂) :
    VMPath nfa wf it.next k (update₁ ++ update₂)

namespace VMPath

theorem eq_or_nfaPath {nfa : NFA} {wf it i update} (path : nfa.VMPath wf it i update) :
  (i.val = nfa.start ∧ update = []) ∨
  ∃ it₀, nfa.Path 0 nfa.start it₀ i it update := by
  induction path with
  | @init it i update cls =>
    simp [εClosure'_iff_path nfa wf] at cls
    cases cls with
    | inl h => simp [←h.1, h.2]
    | inr cls => exact .inr ⟨it, cls⟩
  | @more i j k it update₁ update₂ prev step cls ih =>
    have path₂ : nfa.Path 0 i it k it.next update₂ := by
      simp [εClosure'_iff_path nfa wf] at cls
      match cls with
      | .inl ⟨eqk, equpdate, v⟩ =>
        rw [←eqk, equpdate]
        exact .last step
      | .inr path => exact .more step path

    match ih with
    | .inl ⟨eqi, equpdate⟩ =>
      simp [←eqi, equpdate]
      exact .inr ⟨it, path₂⟩
    | .inr ⟨it₀, path₁⟩ => exact .inr ⟨it₀, path₁.trans path₂⟩

theorem nfaPath_of_ne {nfa : NFA} {wf it i update} (path : nfa.VMPath wf it i update)
  (ne : i.val ≠ nfa.start):
  ∃ it₀, nfa.Path 0 nfa.start it₀ i it update := by
  simpa [ne] using eq_or_nfaPath path

end VMPath

end Regex.NFA

namespace Regex.VM

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
def WriteUpdate {nfa : NFA} (i : Fin nfa.nodes.size) : Prop :=
  match nfa[i] with
  | .done | .char _ _ | .sparse _ _ => True
  | _ => False

/--
All states in `next.state` have a corresponding path from `nfa.start` to the state ending at `it`,
and their updates are written to `next.updates` when necessary.
-/
def SearchState.Inv (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (next : SearchState HistoryStrategy nfa) : Prop :=
  ∀ i ∈ next.states,
    ∃ update,
      nfa.VMPath wf it i update ∧
      (WriteUpdate i → next.updates[i] = update)

theorem SearchState.Inv.of_empty {nfa wf it} {next : SearchState HistoryStrategy nfa} (h : next.states.isEmpty) :
  next.Inv nfa wf it := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

end Regex.VM

theorem Regex.NFA.CharStep.write_update {nfa : NFA} {it i j}
  (step : nfa.CharStep it i j) : Regex.VM.WriteUpdate i := by
  match hn : nfa[i] with
  | .char c next => simp [hn, VM.WriteUpdate]
  | .sparse cs next => simp [hn, VM.WriteUpdate]
  | .done | .fail | .epsilon _ => simp_all
  | .anchor _ _ => simp [anchor hn] at step
  | .split _ _ => simp [split hn] at step
  | .save _ _ => simp [save hn] at step
