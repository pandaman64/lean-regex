import Regex.Data.SparseSet
import Regex.VM
import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (ValidPos)

namespace Regex.NFA

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {pos₀ pos pos' : ValidPos s} {i j : Fin nfa.nodes.size} {update : Option (Nat × ValidPos s)}

@[grind →]
theorem Step.εStep_or_charStep {i j : Nat} (wf : nfa.WellFormed) (step : nfa.Step 0 i pos j pos' update) :
  (nfa.εStep' pos ⟨i, step.lt⟩ ⟨j, step.lt_right wf⟩ update ∧ pos' = pos) ∨
  (nfa.CharStep pos ⟨i, step.lt⟩ ⟨j, step.lt_right wf⟩ ∧ update = .none ∧ ∃ ne, pos' = pos.next ne) := by
  grind

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) (pos₀ : ValidPos s) : ValidPos s → Fin nfa.nodes.size → List (Nat × ValidPos s) → Prop where
  | init {pos i update} (le : pos₀ ≤ pos) (cls : nfa.εClosure' pos ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf pos₀ pos i update
  | more {i j k pos pos' update₁ update₂ update₃} (prev : VMPath nfa wf pos₀ pos i update₁) (step : nfa.CharStep pos i j) (cls : nfa.εClosure' (pos.next step.ne) j k update₂)
    (hupdate : update₃ = update₁ ++ update₂) (hpos : pos' = pos.next step.ne) :
    VMPath nfa wf pos₀ pos' k update₃

namespace VMPath

theorem more_εStep {update₁ update₂}
  (prev : nfa.VMPath wf pos₀ pos i update₁) (step : nfa.εStep' pos i j update₂) :
  nfa.VMPath wf pos₀ pos j (update₁ ++ List.ofOption update₂) := by
  cases prev with
  | init le cls => exact .init le (cls.snoc step)
  | more prev step' cls hupdate eqit => exact .more prev step' (cls.snoc (eqit ▸ step)) (by simp [hupdate]) eqit

theorem more_charStep {update} (prev : nfa.VMPath wf pos₀ pos i update) (step : nfa.CharStep pos i j) :
  nfa.VMPath wf pos₀ (pos.next step.ne) j update := by
  cases prev with
  | init le cls => exact .more (.init le cls) step .base (by simp) rfl
  | more prev step' cls hupdate eqit => exact .more (.more prev step' cls hupdate eqit) step .base (by simp) rfl

theorem more_step {j : Nat} {update₁ update₂}
  (prev : nfa.VMPath wf pos₀ pos i update₁) (step : nfa.Step 0 i pos j pos' update₂) :
  nfa.VMPath wf pos₀ pos' ⟨j, step.lt_right wf⟩ (update₁ ++ List.ofOption update₂) := by
  match step.εStep_or_charStep wf with
  | .inl ⟨step, hpos⟩ => exact hpos ▸ prev.more_εStep step
  | .inr ⟨step, hupdate, ne, hpos⟩ => simpa [hupdate, hpos] using prev.more_charStep step

theorem le {update} (path : nfa.VMPath wf pos₀ pos i update) :
  pos₀ ≤ pos := by
  induction path with
  | init le _ => exact le
  | @more i j k pos' pos _ _ _ _ _ _ _ hpos ih =>
    rw [hpos]
    exact Nat.le_trans ih (Nat.le_of_lt pos'.lt_next)

theorem εClosure_of_eq_it {update} (path : nfa.VMPath wf pos pos i update) :
  nfa.εClosure' pos ⟨nfa.start, wf.start_lt⟩ i update := by
  cases path with
  | init _ cls => exact cls
  | @more i j k pos' pos _ _ _ prev step _ _ hpos =>
    have le := prev.le
    rw [hpos] at le
    exact (Nat.not_lt_of_ge le pos'.lt_next).elim

theorem eq_or_nfaPath {update} (path : nfa.VMPath wf pos₀ pos i update) :
  (i.val = nfa.start ∧ update = [] ∧ pos₀ ≤ pos) ∨
  ∃ poss, pos₀ ≤ poss ∧ nfa.Path 0 nfa.start poss i pos update := by
  induction path with
  | @init pos i update le cls =>
    simp only [εClosure'_iff_path nfa wf] at cls
    cases cls with
    | inl h => simp [←h.1, h.2, le]
    | inr cls => exact .inr ⟨pos, le, cls⟩
  | @more i j k pos pos' update₁ update₂ update₃ prev step cls hupdate hpos ih =>
    have path₂ : nfa.Path 0 i pos k (pos.next step.ne) update₂ := by
      simp only [εClosure'_iff_path nfa wf] at cls
      match cls with
      | .inl ⟨eqk, hupdate⟩ =>
        rw [←eqk, hupdate]
        exact .last step.step
      | .inr path => exact .more step.step path
    match ih with
    | .inl ⟨eqi, hupdate', le⟩ =>
      simp only [← eqi]
      simp only [hupdate'] at hupdate
      exact .inr ⟨pos, le, hupdate ▸ hpos ▸ path₂⟩
    | .inr ⟨poss, le, path₁⟩ => exact .inr ⟨poss, le, hupdate ▸ hpos ▸ path₁.trans path₂⟩

theorem nfaPath_of_ne {update} (path : nfa.VMPath wf pos₀ pos i update) (ne : i.val ≠ nfa.start) :
  ∃ poss, pos₀ ≤ poss ∧ nfa.Path 0 nfa.start poss i pos update := by
  simpa [ne] using eq_or_nfaPath path

theorem concat_nfaPath {i j : Nat} {update₁ update₂} (isLt₁ : i < nfa.nodes.size)
  (path₁ : nfa.VMPath wf pos₀ pos ⟨i, isLt₁⟩ update₁) (path₂ : nfa.Path 0 i pos j pos' update₂) :
  nfa.VMPath wf pos₀ pos' ⟨j, path₂.lt_right wf⟩ (update₁ ++ update₂) := by
  induction path₂ generalizing update₁ with
  | @last j pos k pos' update₂ step => exact path₁.more_step step
  | @more j pos k pos' l pos'' update₂ update₃ step rest ih => simpa using ih rest.lt (path₁.more_step step)

theorem of_nfaPath {i : Nat} {update} (wf : nfa.WellFormed)
  (le : pos₀ ≤ pos) (path : nfa.Path 0 nfa.start pos i pos' update) :
  nfa.VMPath wf pos₀ pos' ⟨i, path.lt_right wf⟩ update := by
  have path₁ : nfa.VMPath wf pos₀ pos ⟨nfa.start, wf.start_lt⟩ [] := .init le .base
  exact path₁.concat_nfaPath wf.start_lt path

end VMPath

end Regex.NFA

namespace Regex.VM

variable {s : String}

/--
The invariant for the soundness theorem.

All states in `next.state` have a corresponding path from `nfa.start` to the state ending at `pos`,
and their updates are written to `next.updates` when necessary.
-/
def SearchState.Inv (nfa : NFA) (wf : nfa.WellFormed) (pos₀ pos : ValidPos s) (next : SearchState (HistoryStrategy s) nfa) : Prop :=
  ∀ i ∈ next.states,
    ∃ update,
      nfa.VMPath wf pos₀ pos i update ∧
      (εClosure.writeUpdate nfa[i] → next.updates[i] = update)

theorem SearchState.Inv.of_empty {nfa wf pos₀ pos} {next : SearchState (HistoryStrategy s) nfa} (h : next.states.isEmpty) :
  next.Inv nfa wf pos₀ pos := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

/--
The invariant for the completeness theorem. The invariant holds only when returning `.none`, since we short-circuit when encountering `.done`.

For all paths ending at `pos`, the state must be tracked in `next.states`. We don't care about the updates for the completeness.
-/
def SearchState.MemOfPathInv (nfa : NFA) (wf : nfa.WellFormed) (pos₀ pos : ValidPos s) (next : SearchState (HistoryStrategy s) nfa) : Prop :=
  ∀ i update, nfa.VMPath wf pos₀ pos i update → i ∈ next.states

/--
Invariant for the completeness theorem.

The `.done` state is not in `next.states`.
-/
def SearchState.NotDoneInv (σ : Strategy s) (nfa : NFA) (next : SearchState σ nfa) : Prop :=
  ∀ i, i ∈ next.states → nfa[i] ≠ .done

theorem SearchState.NotDoneInv.of_empty {σ : Strategy s} {nfa : NFA} {next : SearchState σ nfa} (h : next.states.isEmpty) :
  next.NotDoneInv σ nfa := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

end Regex.VM

theorem Regex.NFA.CharStep.write_update {s : String} {nfa : NFA} {pos : ValidPos s} {i j}
  (step : nfa.CharStep pos i j) : Regex.VM.εClosure.writeUpdate nfa[i] := by
  match step.char_or_sparse with
  | .inl ⟨c, next, eq⟩ => simp [Regex.VM.εClosure.writeUpdate, eq]
  | .inr ⟨cs, next, eq⟩ => simp [Regex.VM.εClosure.writeUpdate, eq]
