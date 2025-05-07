import Regex.Data.SparseSet
import Regex.VM
import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.NFA

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) (it₀ : Iterator) : Iterator → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | init {it i update} (eqs : it.toString = it₀.toString) (le : it₀.pos ≤ it.pos) (cls : nfa.εClosure' it ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf it₀ it i update
  | more {i j k it it' update₁ update₂ update₃} (prev : VMPath nfa wf it₀ it i update₁) (step : nfa.CharStep it i j) (cls : nfa.εClosure' it.next j k update₂)
    (hupdate : update₃ = update₁ ++ update₂) (eqit : it' = it.next) :
    VMPath nfa wf it₀ it' k update₃

namespace VMPath

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
      simp [←eqi, equpdate']
      simp [equpdate'] at equpdate
      exact .inr ⟨it, eqs, le, equpdate ▸ eqit ▸ path₂⟩
    | .inr ⟨itp, eqs, le, path₁⟩ => exact .inr ⟨itp, eqs, le, equpdate ▸ eqit ▸ path₁.trans path₂⟩

theorem nfaPath_of_ne {nfa : NFA} {wf it₀ it i update} (path : nfa.VMPath wf it₀ it i update)
  (ne : i.val ≠ nfa.start):
  ∃ its, its.toString = it₀.toString ∧ it₀.pos ≤ its.pos ∧ nfa.Path 0 nfa.start its i it update := by
  simpa [ne] using eq_or_nfaPath path

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

end Regex.VM

theorem Regex.NFA.CharStep.write_update {nfa : NFA} {it i j}
  (step : nfa.CharStep it i j) : Regex.VM.εClosure.writeUpdate nfa[i] := by
  match step.char_or_sparse with
  | .inl ⟨c, next, eq⟩ => simp [Regex.VM.εClosure.writeUpdate, eq]
  | .inr ⟨cs, next, eq⟩ => simp [Regex.VM.εClosure.writeUpdate, eq]
