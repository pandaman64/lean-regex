import RegexCorrectness.VM.EpsilonClosure

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

set_option linter.unusedVariables false in
theorem eachStepChar.go.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (current : SearchState σ nfa)
  (motive : (i : Nat) → i ≤ current.states.count → SearchState σ nfa → Prop)
  (base : ∀ next, motive current.states.count (Nat.le_refl _) next)
  (done : ∀ i hlt next (hn : nfa[current.states[i]] = .done), motive i (Nat.le_of_lt hlt) next)
  (found : ∀ i hlt next (hn : nfa[current.states[i]] ≠ .done) matched next',
    stepChar σ nfa wf it current.updates next current.states[i] = (matched, next') →
    matched.isSome → motive i (Nat.le_of_lt hlt) next)
  (not_found : ∀ i hlt next (hn : nfa[current.states[i]] ≠ .done) matched next',
    stepChar σ nfa wf it current.updates next current.states[i] = (matched, next') →
    ¬matched.isSome → motive (i + 1) (by omega) next' →
    motive i (Nat.le_of_lt hlt) next)
  (i : Nat) (hle : i ≤ current.states.count) (next : SearchState σ nfa) :
  motive i hle next := by
  refine eachStepChar.go.induct σ nfa wf it current motive ?base ?done ?found ?not_found i hle next
  case base =>
    intro next _
    exact base next
  case done =>
    intro i _ next _ hlt state hn
    exact done i hlt next hn
  case found =>
    intro i _ next _ hlt state hn result isSome
    exact found i hlt next hn result.1 result.2 rfl isSome
  case not_found =>
    intro i _ next _ hlt state hn result notSome ih
    exact not_found i hlt next hn result.1 result.2 rfl (by simp [notSome]) ih

@[simp]
theorem eachStepChar.go_base {σ nfa wf it current next} :
  eachStepChar.go σ nfa wf it current current.states.count (Nat.le_refl _) next = (.none, next) := by
  simp [eachStepChar.go]

@[simp]
theorem eachStepChar.go_done {σ nfa wf it current i next}
  (hlt : i < current.states.count)
  (hn : nfa[current.states[i]] = .done) :
  eachStepChar.go σ nfa wf it current i (Nat.le_of_lt hlt) next = (.none, next) := by
  unfold eachStepChar.go
  simp [Nat.ne_of_lt hlt, hn]

@[simp]
theorem eachStepChar.go_found {σ nfa wf it current i next next' matched}
  (hlt : i < current.states.count)
  (hn : nfa[current.states[i]] ≠ .done)
  (h : stepChar σ nfa wf it current.updates next current.states[i] = (matched, next')) (found : matched.isSome) :
  eachStepChar.go σ nfa wf it current i (Nat.le_of_lt hlt) next = (matched, next') := by
  unfold eachStepChar.go
  simp_all [Nat.ne_of_lt hlt]

@[simp]
theorem eachStepChar.go_not_found {σ nfa wf it current i next next' matched}
  (hlt : i < current.states.count)
  (hn : nfa[current.states[i]] ≠ .done)
  (h : stepChar σ nfa wf it current.updates next current.states[i] = (matched, next')) (not_found : ¬matched.isSome) :
  eachStepChar.go σ nfa wf it current i (Nat.le_of_lt hlt) next = eachStepChar.go σ nfa wf it current (i + 1) (by omega) next' := by
  simp at hn
  conv =>
    lhs
    unfold eachStepChar.go
    simp [Nat.ne_of_lt hlt, hn, h, not_found]

end Regex.VM
