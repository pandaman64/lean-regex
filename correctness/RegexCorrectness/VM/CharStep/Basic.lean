import RegexCorrectness.VM.EpsilonClosure

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

@[simp]
theorem stepChar_char {σ nfa wf it currentUpdates next state c state'} (hn : nfa[state] = .char c state') :
  stepChar σ nfa wf it currentUpdates next state =
  if it.curr = c then
    εClosure σ nfa wf it.next .none next [(currentUpdates.get state, ⟨state', by exact wf.inBounds' state hn⟩)]
  else
    (.none, next) := by
  unfold stepChar
  split <;> simp_all
  next c' state'' hn' =>
    simp [hn'] at hn
    simp [hn]
  next cs state'' hn' =>
    simp [hn'] at hn

@[simp]
theorem stepChar_sparse {σ nfa wf it currentUpdates next state cs state'} (hn : nfa[state] = .sparse cs state') :
  stepChar σ nfa wf it currentUpdates next state =
  if it.curr ∈ cs then
    εClosure σ nfa wf it.next .none next [(currentUpdates.get state, ⟨state', by exact wf.inBounds' state hn⟩)]
  else
    (.none, next) := by
  unfold stepChar
  split <;> simp_all
  next c' state'' hn' =>
    simp [hn'] at hn
  next cs' state'' hn' =>
    simp [hn'] at hn
    simp [hn]

@[simp]
theorem stepChar_not_char_sparse {σ nfa wf it currentUpdates next state}
  (h₁ : ∀ (c : Char) (state' : Nat), nfa[state] = NFA.Node.char c state' → False)
  (h₂ : ∀ (cs : Data.Classes) (state' : Nat), nfa[state] = NFA.Node.sparse cs state' → False) :
  stepChar σ nfa wf it currentUpdates next state = (.none, next) := by
  unfold stepChar
  split <;> simp_all

theorem eachStepChar.go.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (current : SearchState σ nfa)
  (motive : (i : Nat) → i ≤ current.states.count → SearchState σ nfa → Prop)
  (base : ∀ next, motive current.states.count (Nat.le_refl _) next)
  (found : ∀ i hlt next matched next',
    stepChar σ nfa wf it current.updates next current.states[i] = (matched, next') →
    matched.isSome → motive i (Nat.le_of_lt hlt) next)
  (not_found : ∀ i hlt next matched next',
    stepChar σ nfa wf it current.updates next current.states[i] = (matched, next') →
    ¬matched.isSome → motive (i + 1) (by omega) next' →
    motive i (Nat.le_of_lt hlt) next)
  (i : Nat) (hle : i ≤ current.states.count) (next : SearchState σ nfa) :
  motive i hle next := by
  refine eachStepChar.go.induct σ nfa wf it current motive ?base ?found ?not_found i hle next
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
theorem eachStepChar.go_base {σ nfa wf it current next} :
  eachStepChar.go σ nfa wf it current current.states.count (Nat.le_refl _) next = (.none, next) := by
  simp [eachStepChar.go]

@[simp]
theorem eachStepChar.go_found {σ nfa wf it current i next next' matched}
  (hlt : i < current.states.count)
  (h : stepChar σ nfa wf it current.updates next current.states[i] = (matched, next')) (found : matched.isSome) :
  eachStepChar.go σ nfa wf it current i (Nat.le_of_lt hlt) next = (matched, next') := by
  unfold eachStepChar.go
  simp [Nat.ne_of_lt hlt, h, found]

@[simp]
theorem eachStepChar.go_not_found {σ nfa wf it current i next next' matched}
  (hlt : i < current.states.count)
  (h : stepChar σ nfa wf it current.updates next current.states[i] = (matched, next')) (not_found : ¬matched.isSome) :
  eachStepChar.go σ nfa wf it current i (Nat.le_of_lt hlt) next = eachStepChar.go σ nfa wf it current (i + 1) (by omega) next' := by
  conv =>
    lhs
    unfold eachStepChar.go
    simp [Nat.ne_of_lt hlt, h, not_found]

end Regex.VM
