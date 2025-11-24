import Regex.Data.SparseSet
import Regex.VM
import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Iterator)
open String.Pos (Raw)

namespace Regex.NFA

theorem Step.εStep_or_charStep {nfa : NFA} {it it' i j update} (wf : nfa.WellFormed) (step : nfa.Step 0 i it j it' update) :
  (nfa.εStep' it ⟨i, step.lt⟩ ⟨j, step.lt_right wf⟩ update ∧ it' = it) ∨
  (nfa.CharStep it ⟨i, step.lt⟩ ⟨j, step.lt_right wf⟩ ∧ it' = it.next ∧ update = .none) := by
  cases step with
  | epsilon ge lt v eq => exact .inl ⟨Step.epsilon ge lt v eq, rfl⟩
  | anchor ge lt eq v htest => exact .inl ⟨Step.anchor ge lt eq v htest, rfl⟩
  | splitLeft ge lt eq v => exact .inl ⟨Step.splitLeft ge lt eq v, rfl⟩
  | splitRight ge lt eq v => exact .inl ⟨Step.splitRight ge lt eq v, rfl⟩
  | save ge lt eq v => exact .inl ⟨Step.save ge lt eq v, rfl⟩
  | char ge lt eq vf => exact .inr ⟨Step.char ge lt eq vf, rfl, rfl⟩
  | sparse ge lt eq mem vf => exact .inr ⟨Step.sparse ge lt eq mem vf, rfl, rfl⟩

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) (it₀ : Iterator) : Iterator → Fin nfa.nodes.size → List (Nat × Raw) → Prop where
  | init {it i update} (eqs : it.toString = it₀.toString) (le : it₀.pos ≤ it.pos) (cls : nfa.εClosure' it ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf it₀ it i update
  | more {i j k it it' update₁ update₂ update₃} (prev : VMPath nfa wf it₀ it i update₁) (step : nfa.CharStep it i j) (cls : nfa.εClosure' it.next j k update₂)
    (hupdate : update₃ = update₁ ++ update₂) (eqit : it' = it.next) :
    VMPath nfa wf it₀ it' k update₃

namespace VMPath

theorem more_εStep {nfa : NFA} {wf it₀ it i j update₁ update₂}
  (prev : nfa.VMPath wf it₀ it i update₁) (step : nfa.εStep' it i j update₂) :
  nfa.VMPath wf it₀ it j (update₁ ++ List.ofOption update₂) := by
  cases prev with
  | init eqs le cls => exact .init eqs le (cls.snoc step)
  | more prev step' cls hupdate eqit => exact .more prev step' (cls.snoc (eqit ▸ step)) (by simp [hupdate]) eqit

theorem more_charStep {nfa : NFA} {wf it₀ it i j update}
  (prev : nfa.VMPath wf it₀ it i update) (step : nfa.CharStep it i j) :
  nfa.VMPath wf it₀ it.next j update := by
  cases prev with
  | init eqs le cls => exact .more (.init eqs le cls) step (.base step.validR) (by simp) rfl
  | more prev step' cls hupdate eqit => exact .more (.more prev step' cls hupdate eqit) step (.base step.validR) (by simp) rfl

theorem more_step {nfa : NFA} {wf it₀ it it' i j update₁ update₂}
  (prev : nfa.VMPath wf it₀ it i update₁) (step : nfa.Step 0 i it j it' update₂) :
  nfa.VMPath wf it₀ it' ⟨j, step.lt_right wf⟩ (update₁ ++ List.ofOption update₂) := by
  match step.εStep_or_charStep wf with
  | .inl ⟨step, eqit⟩ => exact eqit ▸ prev.more_εStep step
  | .inr ⟨step, eqit, equpdate⟩ => simpa [eqit, equpdate] using prev.more_charStep step

theorem valid {nfa : NFA} {wf it₀ it i update} (path : nfa.VMPath wf it₀ it i update) : it.Valid := by
  cases path with
  | init _ _ cls => exact cls.valid
  | more _ _ cls _ eqit => exact eqit ▸ cls.valid

theorem toString {nfa : NFA} {wf it₀ it i update} (path : nfa.VMPath wf it₀ it i update) :
  it.toString = it₀.toString := by
  induction path with
  | init eqs => exact eqs
  | more _ _ _ _ eqit ih =>
    rw [eqit, Iterator.next_toString, ih]

theorem le_pos {nfa : NFA} {wf it₀ it i update} (path : nfa.VMPath wf it₀ it i update) :
  it₀.pos ≤ it.pos := by
  induction path with
  | init _ le _ => exact le
  | @more i j k it' it _ _ _ _ _ _ _ eqit ih =>
    rw [eqit]
    exact Nat.le_trans ih (Nat.le_of_lt it'.lt_next)

theorem εClosure_of_eq_it {nfa : NFA} {wf it i update} (path : nfa.VMPath wf it it i update) :
  nfa.εClosure' it ⟨nfa.start, wf.start_lt⟩ i update := by
  cases path with
  | init _ _ cls => exact cls
  | @more i j k it' it _ _ _ prev step _ _ eqit =>
    have le := prev.le_pos
    rw [eqit] at le
    exact (Nat.not_lt_of_ge le it'.lt_next).elim

theorem eq_or_nfaPath {nfa : NFA} {wf it₀ it i update} (path : nfa.VMPath wf it₀ it i update) :
  (i.val = nfa.start ∧ update = [] ∧ it.toString = it₀.toString ∧ it₀.pos ≤ it.pos) ∨
  ∃ its, its.toString = it₀.toString ∧ it₀.pos ≤ its.pos ∧ nfa.Path 0 nfa.start its i it update := by
  induction path with
  | @init itp i update eqs le cls =>
    simp [εClosure'_iff_path nfa wf] at cls
    cases cls with
    | inl h => simp [←h.1, h.2, eqs, le, -Iterator.toString, -Iterator.pos]
    | inr cls => exact .inr ⟨itp, eqs, le, cls⟩
  | @more i j k it it' update₁ update₂ update₃ prev step cls equpdate eqit ih =>
    have path₂ : nfa.Path 0 i it k it.next update₂ := by
      simp [εClosure'_iff_path nfa wf] at cls
      match cls with
      | .inl ⟨eqk, equpdate, v⟩ =>
        rw [←eqk, equpdate]
        exact .last step
      | .inr path => exact .more step path

    match ih with
    | .inl ⟨eqi, equpdate', eqs, le⟩ =>
      simp [←eqi]
      simp [equpdate'] at equpdate
      exact .inr ⟨it, eqs, le, equpdate ▸ eqit ▸ path₂⟩
    | .inr ⟨itp, eqs, le, path₁⟩ => exact .inr ⟨itp, eqs, le, equpdate ▸ eqit ▸ path₁.trans path₂⟩

theorem nfaPath_of_ne {nfa : NFA} {wf it₀ it i update} (path : nfa.VMPath wf it₀ it i update)
  (ne : i.val ≠ nfa.start):
  ∃ its, its.toString = it₀.toString ∧ it₀.pos ≤ its.pos ∧ nfa.Path 0 nfa.start its i it update := by
  simpa [ne] using eq_or_nfaPath path

theorem concat_nfaPath {nfa : NFA} {wf it₀ it it' i j update₁ update₂}
  (isLt₁ : i < nfa.nodes.size)
  (path₁ : nfa.VMPath wf it₀ it ⟨i, isLt₁⟩ update₁) (path₂ : nfa.Path 0 i it j it' update₂) :
  nfa.VMPath wf it₀ it' ⟨j, path₂.lt_right wf⟩ (update₁ ++ update₂) := by
  induction path₂ generalizing update₁ with
  | @last j it k it' update₂ step => exact path₁.more_step step
  | @more j it k it' l it'' update₂ update₃ step rest ih => simpa using ih rest.lt (path₁.more_step step)

theorem of_nfaPath {nfa : NFA} {it₀ it it' i update} (wf : nfa.WellFormed)
  (eqs : it.toString = it₀.toString) (le : it₀.pos ≤ it.pos)
  (path : nfa.Path 0 nfa.start it i it' update) :
  nfa.VMPath wf it₀ it' ⟨i, path.lt_right wf⟩ update := by
  have path₁ : nfa.VMPath wf it₀ it ⟨nfa.start, wf.start_lt⟩ [] := .init eqs le (.base path.validL)
  exact path₁.concat_nfaPath wf.start_lt path

end VMPath

end Regex.NFA

namespace Regex.VM

/--
The invariant for the soundness theorem.

All states in `next.state` have a corresponding path from `nfa.start` to the state ending at `it`,
and their updates are written to `next.updates` when necessary.
-/
def SearchState.Inv (nfa : NFA) (wf : nfa.WellFormed) (it₀ it : Iterator) (next : SearchState HistoryStrategy nfa) : Prop :=
  ∀ i ∈ next.states,
    ∃ update,
      nfa.VMPath wf it₀ it i update ∧
      (εClosure.writeUpdate nfa[i] → next.updates[i] = update)

theorem SearchState.Inv.of_empty {nfa wf it₀ it} {next : SearchState HistoryStrategy nfa} (h : next.states.isEmpty) :
  next.Inv nfa wf it₀ it := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

/--
The invariant for the completeness theorem. The invariant holds only when returning `.none`, since we short-circuit when encountering `.done`.

For all paths ending at `it`, the state must be tracked in `next.states`. We don't care about the updates for the completeness.
-/
def SearchState.MemOfPathInv (nfa : NFA) (wf : nfa.WellFormed) (it₀ it : Iterator) (next : SearchState HistoryStrategy nfa) : Prop :=
  ∀ i update, nfa.VMPath wf it₀ it i update → i ∈ next.states

/--
Invariant for the completeness theorem.

The `.done` state is not in `next.states`.
-/
def SearchState.NotDoneInv (σ : Strategy) (nfa : NFA) (next : SearchState σ nfa) : Prop :=
  ∀ i, i ∈ next.states → nfa[i] ≠ .done

theorem SearchState.NotDoneInv.of_empty {σ nfa} {next : SearchState σ nfa} (h : next.states.isEmpty) :
  next.NotDoneInv σ nfa := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

end Regex.VM

theorem Regex.NFA.CharStep.write_update {nfa : NFA} {it i j}
  (step : nfa.CharStep it i j) : Regex.VM.εClosure.writeUpdate nfa[i] := by
  match step.char_or_sparse with
  | .inl ⟨c, next, eq⟩ => simp [Regex.VM.εClosure.writeUpdate, eq]
  | .inr ⟨cs, next, eq⟩ => simp [Regex.VM.εClosure.writeUpdate, eq]
