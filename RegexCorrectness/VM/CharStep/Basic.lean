import RegexCorrectness.VM.EpsilonClosure

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

/--
If the given state can make a transition on the current character of `it`, make the transition and
traverse ε-closures from the resulting state.
-/
def stepChar' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (next : SparseSet nfa.nodes.size) (updates : Vec (List (Nat × Pos)) nfa.nodes.size)
  (state : Fin nfa.nodes.size) :
  (SparseSet nfa.nodes.size × Option (List (Nat × String.Pos)) × Vec (List (Nat × String.Pos)) nfa.nodes.size) :=
  match hn : nfa[state] with
  | .char c state' =>
    if it.curr = c then
      have isLt := wf.inBounds' state hn
      let update := updates.get state state.isLt
      εClosure' nfa wf it.next next .none updates [(update, ⟨state', isLt⟩)]
    else
      (next, .none, updates)
  | .sparse cs state' =>
    if it.curr ∈ cs then
      have isLt := wf.inBounds' state hn
      let update := updates.get state state.isLt
      εClosure' nfa wf it.next next .none updates [(update, ⟨state', isLt⟩)]
    else
      (next, .none, updates)
  | _ => (next, .none, updates)

/--
For all states in `current`, make a transition on the current character of `it` and traverse
ε-closures from the resulting states.
-/
def eachStepChar' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (current : SparseSet nfa.nodes.size) (next : SparseSet nfa.nodes.size)
  (updates : Vec (List (Nat × Pos)) nfa.nodes.size) :
  (SparseSet nfa.nodes.size × Option (List (Nat × String.Pos)) × Vec (List (Nat × String.Pos)) nfa.nodes.size) :=
  go 0 (Nat.zero_le _) next updates
where
  go (i : Nat) (hle : i ≤ current.count) (next : SparseSet nfa.nodes.size) (updates : Vec (List (Nat × Pos)) nfa.nodes.size) :
    (SparseSet nfa.nodes.size × Option (List (Nat × String.Pos)) × Vec (List (Nat × String.Pos)) nfa.nodes.size) :=
    if h : i = current.count then
      (next, .none, updates)
    else
      have hlt : i < current.count := Nat.lt_of_le_of_ne hle h
      let result := stepChar' nfa wf it next updates current[i]
      if result.2.1.isSome then
        result
      else
        go (i + 1) hlt result.1 result.2.2

theorem eachStepChar'.go.induct' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (current : SparseSet nfa.nodes.size)
  (motive : (i : Nat) → i ≤ current.count → SparseSet nfa.nodes.size → Vec (List (Nat × Pos)) nfa.nodes.size → Prop)
  (base : ∀ next updates, motive current.count (Nat.le_refl _) next updates)
  (found : ∀ i next updates hlt next' matched updates',
    stepChar' nfa wf it next updates current[i] = (next', matched, updates') →
    matched.isSome → motive i (Nat.le_of_lt hlt) next updates)
  (not_found : ∀ i next updates hlt next' matched updates',
    stepChar' nfa wf it next updates current[i] = (next', matched, updates') →
    ¬matched.isSome → motive (i + 1) (by omega) next' updates' →
    motive i (Nat.le_of_lt hlt) next updates)
  (i : Nat) (hle : i ≤ current.count) (next : SparseSet nfa.nodes.size) (updates : Vec (List (Nat × Pos)) nfa.nodes.size) :
  motive i hle next updates := by
  refine eachStepChar'.go.induct nfa wf it current motive ?base ?found ?not_found i hle next updates
  case base =>
    intro next updates _
    exact base next updates
  case found =>
    intro i _ next updates _ hlt result isSome
    exact found i next updates hlt result.1 result.2.1 result.2.2 rfl isSome
  case not_found =>
    intro i _ next updates _ hlt result notSome ih
    exact not_found i next updates hlt result.1 result.2.1 result.2.2 rfl notSome ih

end Regex.VM
