import Regex.Data.SparseSet
import Regex.NFA.Basic
import Regex.VM
import RegexCorrectness.VM.Path

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

abbrev εStack' (nfa : NFA) := List (List (Nat × Pos) × Fin nfa.nodes.size)

/--
A version of εClosure traversal that tracks the updates to the capture groups.

As the NFA semantics use `List (Nat × Pos)` to represent the capture group updates, this
εClosure implementation also use it for verification. The actual VM implementation materializes the
updates as a `Buffer` for efficiency, and the correspondence will be proved in `Correspondence.lean`.
-/
def εClosure' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (matched : Option (List (Nat × Pos))) (next : SearchState' nfa) (stack : εStack' nfa) :
  Option (List (Nat × Pos)) × SearchState' nfa :=
  match stack with
  | [] => (matched, next)
  | (update, state) :: stack' =>
    if state ∈ next.states then
      εClosure' nfa wf it matched next stack'
    else
      let states' := next.states.insert state
      match hn : nfa[state] with
      | .epsilon state' =>
        have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
        εClosure' nfa wf it matched ⟨states', next.updates⟩ ((update, ⟨state', isLt⟩) :: stack')
      | .split state₁ state₂ =>
        have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
        εClosure' nfa wf it matched ⟨states', next.updates⟩ ((update, ⟨state₁, isLt.1⟩) :: (update, ⟨state₂, isLt.2⟩):: stack')
      | .save offset state' =>
        have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
        let update' := update ++ [(offset, it.pos)]
        εClosure' nfa wf it matched ⟨states', next.updates⟩ ((update', ⟨state', isLt⟩) :: stack')
      | .done =>
        let matched' := matched <|> update
        let updates' := next.updates.set state update
        εClosure' nfa wf it matched' ⟨states', updates'⟩ stack'
      | .char c state' =>
        let updates' := next.updates.set state update
        εClosure' nfa wf it matched ⟨states', updates'⟩ stack'
      | .sparse cs state' =>
        let updates' := next.updates.set state update
        εClosure' nfa wf it matched ⟨states', updates'⟩ stack'
      | .fail => εClosure' nfa wf it matched ⟨states', next.updates⟩ stack'
termination_by (next.states.measure, stack)

-- Cleaner version of the fuction induction principle
-- Using tactics in the body crashes Lean due to too high memory usage
theorem εClosure'.induct' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (motive : Option (List (Nat × Pos)) → SearchState' nfa → εStack' nfa → Prop)
  (base : ∀ matched next, motive matched next [])
  (visited :
    ∀ matched next update state stack',
    state ∈ next.states →
    motive matched next stack' →
    motive matched next ((update, state) :: stack'))
  (epsilon : ∀ matched next update state stack' state',
    state ∉ next.states → nfa[state] = .epsilon state' →
    let next' := ⟨next.states.insert state, next.updates⟩;
    motive matched next' ((update, state') :: stack') →
    motive matched next ((update, state) :: stack'))
  (split : ∀ matched next update state stack' state₁ state₂,
    state ∉ next.states → nfa[state] = .split state₁ state₂ →
    let next' := ⟨next.states.insert state, next.updates⟩;
    motive matched next' ((update, state₁) :: (update, state₂) :: stack') →
    motive matched next ((update, state) :: stack'))
  (save : ∀ matched next update state stack' offset state',
    state ∉ next.states → nfa[state] = .save offset state' →
    let next' := ⟨next.states.insert state, next.updates⟩;
    motive matched next' ((update ++ [(offset, it.pos)], state') :: stack') →
    motive matched next ((update, state) :: stack'))
  (done : ∀ matched next update state stack',
    state ∉ next.states → nfa[state] = .done →
    let next' := ⟨next.states.insert state, next.updates.set state update⟩;
    motive (matched <|> .some update) next' stack' →
    motive matched next ((update, state) :: stack'))
  (char : ∀ matched next update state stack' c (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .char c state' →
    let next' := ⟨next.states.insert state, next.updates.set state update⟩;
    motive matched next' stack' →
    motive matched next ((update, state) :: stack'))
  (sparse : ∀ matched next update state stack' cs (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .sparse cs state' →
    let next' := ⟨next.states.insert state, next.updates.set state update⟩;
    motive matched next' stack' →
    motive matched next ((update, state) :: stack'))
  (fail : ∀ matched next update state stack',
    state ∉ next.states → nfa[state] = .fail →
    let next' := ⟨next.states.insert state, next.updates⟩;
    motive matched next' stack' →
    motive matched next ((update, state) :: stack')) :
  ∀ matched next stack, motive matched next stack := fun matched next stack =>
    εClosure'.induct nfa wf it motive base visited
      (fun matched next update state stack' mem state' hn isLt ih =>
        epsilon matched next update state stack' ⟨state', isLt⟩ mem hn ih)
      (fun matched next update state stack' mem state₁ state₂ hn isLt ih =>
        split matched next update state stack' ⟨state₁, isLt.1⟩ ⟨state₂, isLt.2⟩ mem hn ih)
      (fun matched next update state stack' mem offset state' hn isLt ih =>
        save matched next update state stack' offset ⟨state', isLt⟩ mem hn ih)
      (fun matched next update state stack' mem hn ih =>
        done matched next update state stack' mem hn ih)
      (fun matched next update state stack' mem c state' hn ih =>
        char matched next update state stack' c ⟨state', wf.inBounds' state hn⟩ mem hn ih)
      (fun matched next update state stack' mem cs state' hn ih =>
        sparse matched next update state stack' cs ⟨state', wf.inBounds' state hn⟩ mem hn ih)
      (fun matched next update state stack' mem hn ih =>
        fail matched next update state stack' mem hn ih)
      matched next stack

/-
Simplification lemmas for `εClosure'`.
-/
section

variable {nfa wf it matched next}

@[simp]
theorem εClosure'_base : εClosure' nfa wf it matched next [] = (matched, next) := by
  simp [εClosure']

@[simp]
theorem εClosure'_visited {update state stack'} (hmem : state ∈ next.states) :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched next stack' := by
  simp [εClosure', hmem]

@[simp]
theorem εClosure'_epsilon {update state stack' state'} (hmem : state ∉ next.states) (hn : nfa[state] = .epsilon state') :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, state') :: stack') := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_split {update state stack' state₁ state₂} (hmem : state ∉ next.states) (hn : nfa[state] = .split state₁ state₂) :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, state₁) :: (update, state₂) :: stack') := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_save {update state stack' offset state'} (hmem : state ∉ next.states) (hn : nfa[state] = .save offset state') :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update ++ [(offset, it.pos)], state') :: stack') := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_done {update state stack'} (hmem : state ∉ next.states) (hn : nfa[state] = .done) :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it (matched <|> .some update) ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_char {update state stack' c state'} (hmem : state ∉ next.states) (hn : nfa[state] = .char c state') :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_sparse {update state stack' cs state'} (hmem : state ∉ next.states) (hn : nfa[state] = .sparse cs state') :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_fail {update state stack'} (hmem : state ∉ next.states) (hn : nfa[state] = .fail) :
  εClosure' nfa wf it matched next ((update, state) :: stack') =
  εClosure' nfa wf it matched ⟨next.states.insert state, next.updates⟩ stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

end

end Regex.VM
