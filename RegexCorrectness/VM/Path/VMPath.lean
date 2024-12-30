import Regex.Data.SparseSet
import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (Span SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.NFA

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) : Span → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | init {l r i update} (cls : nfa.εClosure' ⟨l, [], r⟩ ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf ⟨l, [], r⟩  i update
  | more {i j k span c r' update₁ update₂} (prev : VMPath nfa wf span i update₁) (h : span.r = c :: r')
    (step : nfa.CharStep span.l span.m c r' i j) (cls : nfa.εClosure' span.next j k update₂) :
    VMPath nfa wf span.next k (update₁ ++ update₂)

end Regex.NFA

namespace Regex.VM

structure SearchState' (nfa : NFA) where
  states : SparseSet nfa.nodes.size
  updates : Vec (List (Nat × Pos)) nfa.nodes.size

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
def WriteUpdate {nfa : NFA} (i : Fin nfa.nodes.size) : Prop :=
  match nfa[i] with
  | .done | .char _ _ | .sparse _ _ => True
  | _ => False

/--
All states in `next.state` have a corresponding path from `nfa.start` to the state where the span
ends at `it`, and their updates are written to `next.updates` when necessary.
-/
def SearchState'.Inv (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (next : SearchState' nfa) : Prop :=
  ∀ i ∈ next.states,
    ∃ span update,
      span.iterator = it ∧
      nfa.VMPath wf span i update ∧
      (WriteUpdate i → next.updates[i] = update)

theorem SearchState'.Inv.of_empty {nfa wf it} {next : SearchState' nfa} (h : next.states.isEmpty) :
  next.Inv nfa wf it := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

end Regex.VM

theorem Regex.NFA.CharStep.write_update {nfa : NFA} {l m c r i j}
  (step : nfa.CharStep l m c r i j) : Regex.VM.WriteUpdate i := by
  cases step <;> simp_all [VM.WriteUpdate]
