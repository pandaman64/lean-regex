import RegexCorrectness.VM.EpsilonClosure

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

/--
If the given state can make a transition on the current character of `it`, make the transition and
traverse ε-closures from the resulting state.
-/
def stepChar' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (currentUpdates : Vector (List (Nat × Pos)) nfa.nodes.size)
  (next : SearchState' nfa) (state : Fin nfa.nodes.size) :
  Option (List (Nat × Pos)) × SearchState' nfa :=
  match hn : nfa[state] with
  | .char c state' =>
    if it.curr = c then
      have isLt := wf.inBounds' state hn
      let update := currentUpdates.get state
      εClosure' nfa wf it.next .none next [(update, ⟨state', isLt⟩)]
    else
      (.none, next)
  | .sparse cs state' =>
    if it.curr ∈ cs then
      have isLt := wf.inBounds' state hn
      let update := currentUpdates.get state
      εClosure' nfa wf it.next .none next [(update, ⟨state', isLt⟩)]
    else
      (.none, next)
  | _ => (.none, next)

/--
For all states in `current`, make a transition on the current character of `it` and traverse
ε-closures from the resulting states.
-/
def eachStepChar' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (current : SearchState' nfa) (next : SearchState' nfa) :
  Option (List (Nat × Pos)) × SearchState' nfa :=
  go 0 (Nat.zero_le _) next
where
  go (i : Nat) (hle : i ≤ current.states.count) (next : SearchState' nfa) :
    Option (List (Nat × Pos)) × SearchState' nfa :=
    if h : i = current.states.count then
      (.none, next)
    else
      have hlt : i < current.states.count := Nat.lt_of_le_of_ne hle h
      let result := stepChar' nfa wf it current.updates next current.states[i]
      if result.1.isSome then
        result
      else
        go (i + 1) hlt result.2

theorem eachStepChar'.go.induct' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (current : SearchState' nfa)
  (motive : (i : Nat) → i ≤ current.states.count → SearchState' nfa → Prop)
  (base : ∀ next, motive current.states.count (Nat.le_refl _) next)
  (found : ∀ i hlt next matched next',
    stepChar' nfa wf it current.updates next current.states[i] = (matched, next') →
    matched.isSome → motive i (Nat.le_of_lt hlt) next)
  (not_found : ∀ i hlt next matched next',
    stepChar' nfa wf it current.updates next current.states[i] = (matched, next') →
    ¬matched.isSome → motive (i + 1) (by omega) next' →
    motive i (Nat.le_of_lt hlt) next)
  (i : Nat) (hle : i ≤ current.states.count) (next : SearchState' nfa) :
  motive i hle next := by
  refine eachStepChar'.go.induct nfa wf it current motive ?base ?found ?not_found i hle next
  case base =>
    intro next _
    exact base next
  case found =>
    intro i _ next _ hlt result isSome
    exact found i hlt next result.1 result.2 rfl isSome
  case not_found =>
    intro i _ next _ hlt result notSome ih
    exact not_found i hlt next result.1 result.2 rfl (by simp [notSome]) ih

@[simp]
theorem eachStepChar'.go_base {nfa wf it current next} :
  eachStepChar'.go nfa wf it current current.states.count (Nat.le_refl _) next = (.none, next) := by
  simp [eachStepChar'.go]

@[simp]
theorem eachStepChar'.go_found {nfa wf it current i next next' matched}
  (hlt : i < current.states.count)
  (h : stepChar' nfa wf it current.updates next current.states[i] = (matched, next')) (found : matched.isSome) :
  eachStepChar'.go nfa wf it current i (Nat.le_of_lt hlt) next = (matched, next') := by
  unfold eachStepChar'.go
  simp [Nat.ne_of_lt hlt, h, found]

@[simp]
theorem eachStepChar'.go_not_found {nfa wf it current i next next' matched}
  (hlt : i < current.states.count)
  (h : stepChar' nfa wf it current.updates next current.states[i] = (matched, next')) (not_found : ¬matched.isSome) :
  eachStepChar'.go nfa wf it current i (Nat.le_of_lt hlt) next = eachStepChar'.go nfa wf it current (i + 1) (by omega) next' := by
  conv =>
    lhs
    unfold eachStepChar'.go
    simp [Nat.ne_of_lt hlt, h, not_found]

end Regex.VM
