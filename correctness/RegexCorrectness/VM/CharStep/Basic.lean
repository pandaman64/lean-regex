import RegexCorrectness.VM.EpsilonClosure

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos)

namespace Regex.VM

set_option linter.unusedVariables false in
theorem eachStepChar.go.induct' {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (pos : Pos s) (ne : pos ≠ s.endPos) (current : SearchState σ nfa)
  (motive : (i : Nat) → i ≤ current.states.count → SearchState σ nfa → Prop)
  (base : ∀ next, motive current.states.count (Nat.le_refl _) next)
  (done : ∀ i hlt next (hn : nfa[current.states[i]] = .done), motive i (Nat.le_of_lt hlt) next)
  (found : ∀ i hlt next (hn : nfa[current.states[i]] ≠ .done) matched next',
    stepChar σ nfa wf pos ne current.updates next current.states[i] = (matched, next') →
    matched.isSome → motive i (Nat.le_of_lt hlt) next)
  (not_found : ∀ i hlt next (hn : nfa[current.states[i]] ≠ .done) matched next',
    stepChar σ nfa wf pos ne current.updates next current.states[i] = (matched, next') →
    ¬matched.isSome → motive (i + 1) (by omega) next' →
    motive i (Nat.le_of_lt hlt) next)
  (i : Nat) (hle : i ≤ current.states.count) (next : SearchState σ nfa) :
  motive i hle next := by
  refine eachStepChar.go.induct σ nfa wf pos ne current motive ?base ?done ?found ?not_found i hle next
  case base =>
    intro next _
    exact base next
  case done =>
    intro i _ next _ hlt state hn
    exact done i hlt next (by simpa using hn)
  case found =>
    intro i _ next _ hlt state hn result isSome
    exact found i hlt next (by simpa using hn) result.1 result.2 rfl isSome
  case not_found =>
    intro i _ next _ hlt state hn result notSome ih
    exact not_found i hlt next (by simpa using hn) result.1 result.2 rfl (by simp [notSome]) ih

@[simp, grind =]
theorem eachStepChar.go_base {s : String} {σ : Strategy s} {nfa wf pos ne current next} :
  eachStepChar.go σ nfa wf pos ne current current.states.count (Nat.le_refl _) next = (.none, next) := by
  grind [eachStepChar.go]

@[simp, grind =]
theorem eachStepChar.go_done {s : String} {σ : Strategy s} {nfa wf pos ne current i next}
  (hlt : i < current.states.count)
  (hn : nfa[current.states[i]] = .done) :
  eachStepChar.go σ nfa wf pos ne current i (Nat.le_of_lt hlt) next = (.none, next) := by
  grind [eachStepChar.go]

@[simp, grind →]
theorem eachStepChar.go_found {s : String} {σ : Strategy s} {nfa wf pos ne current i next next' matched}
  (hlt : i < current.states.count)
  (hn : nfa[current.states[i]] ≠ .done)
  (h : stepChar σ nfa wf pos ne current.updates next current.states[i] = (matched, next')) (found : matched.isSome) :
  eachStepChar.go σ nfa wf pos ne current i (Nat.le_of_lt hlt) next = (matched, next') := by
  grind [eachStepChar.go]

@[simp, grind →]
theorem eachStepChar.go_not_found {s : String} {σ : Strategy s} {nfa wf pos ne current i next next' matched}
  (hlt : i < current.states.count)
  (hn : nfa[current.states[i]] ≠ .done)
  (h : stepChar σ nfa wf pos ne current.updates next current.states[i] = (matched, next')) (not_found : ¬matched.isSome) :
  eachStepChar.go σ nfa wf pos ne current i (Nat.le_of_lt hlt) next = eachStepChar.go σ nfa wf pos ne current (i + 1) (by omega) next' := by
  grind [eachStepChar.go]

end Regex.VM
