import Regex.VM.Basic2

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {bufferSize : Nat} {it : Iterator}
  {matched : Option (Buffer bufferSize)} {current next current' next' : SearchState nfa bufferSize}

@[simp]
theorem εClosure_base : εClosure2 nfa wf it matched next [] = (matched, next) := by
  simp [εClosure2]

@[simp]
theorem εClosure_visited {update state stack'} (hmem : state ∈ next.states) :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched next stack' := by
  simp [εClosure2, hmem]

@[simp]
theorem εClosure_epsilon {update state stack' state'} (hmem : state ∉ next.states) (hn : nfa[state] = .epsilon state') :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, ⟨state', wf.inBounds' state hn⟩) :: stack') := by
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp [*] at hn; simp_all

@[simp]
theorem εClosure_split {update state stack' state₁ state₂} (hmem : state ∉ next.states) (hn : nfa[state] = .split state₁ state₂) :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, ⟨state₁, (wf.inBounds' state hn).1⟩) :: (update, ⟨state₂, (wf.inBounds' state hn).2⟩) :: stack') := by
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp [*] at hn; simp_all

@[simp]
theorem εClosure_save {update state stack' offset state'} (hmem : state ∉ next.states) (hn : nfa[state] = .save offset state') :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update.setIfInBounds offset it.pos, ⟨state', wf.inBounds' state hn⟩) :: stack') := by
  simp at hn
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp [*] at hn; simp_all

@[simp]
theorem εClosure_done {update state stack'} (hmem : state ∉ next.states) (hn : nfa[state] = .done) :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it (matched <|> .some update) ⟨next.states.insert state, next.updates.set state state.isLt update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_char {update state stack' c state'} (hmem : state ∉ next.states) (hn : nfa[state] = .char c state') :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched ⟨next.states.insert state, next.updates.set state state.isLt update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_sparse {update state stack' cs state'} (hmem : state ∉ next.states) (hn : nfa[state] = .sparse cs state') :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched ⟨next.states.insert state, next.updates.set state state.isLt update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_fail {update state stack'} (hmem : state ∉ next.states) (hn : nfa[state] = .fail) :
  εClosure2 nfa wf it matched next ((update, state) :: stack') =
  εClosure2 nfa wf it matched ⟨next.states.insert state, next.updates⟩ stack' := by
  conv =>
    lhs
    unfold εClosure2
    simp [hmem]
  split <;> simp_all

@[simp]
theorem stepChar_char {currentUpdates state c state'} (hn : nfa[state] = .char c state') :
  stepChar2 nfa wf it currentUpdates next state =
  if it.curr = c then
    εClosure2 nfa wf it.next .none next [(currentUpdates.get state state.isLt, ⟨state', by exact wf.inBounds' state hn⟩)]
  else
    (.none, next) := by
  unfold stepChar2
  split <;> simp_all
  next c' state'' hn' =>
    simp [hn'] at hn
    simp [hn]
  next cs state'' hn' =>
    simp [hn'] at hn

@[simp]
theorem stepChar_sparse {currentUpdates state cs state'} (hn : nfa[state] = .sparse cs state') :
  stepChar2 nfa wf it currentUpdates next state =
  if it.curr ∈ cs then
    εClosure2 nfa wf it.next .none next [(currentUpdates.get state state.isLt, ⟨state', by exact wf.inBounds' state hn⟩)]
  else
    (.none, next) := by
  unfold stepChar2
  split <;> simp_all
  next c' state'' hn' =>
    simp [hn'] at hn
  next cs' state'' hn' =>
    simp [hn'] at hn
    simp [hn]

@[simp]
theorem stepChar_not_char_sparse {currentUpdates state}
  (h₁ : ∀ (c : Char) (state' : Nat), nfa[state] = NFA.Node.char c state' → False)
  (h₂ : ∀ (cs : Data.Classes) (state' : Nat), nfa[state] = NFA.Node.sparse cs state' → False) :
  stepChar2 nfa wf it currentUpdates next state = (.none, next) := by
  unfold stepChar2
  split <;> simp_all

@[simp]
theorem eachStepChar.go_base :
  eachStepChar2.go nfa wf it current current.states.count (Nat.le_refl _) next = (.none, next) := by
  simp [eachStepChar2.go]

@[simp]
theorem eachStepChar.go_found {i}
  (hlt : i < current.states.count)
  (h : stepChar2 nfa wf it current.updates next current.states[i] = (matched, next')) (found : matched.isSome) :
  eachStepChar2.go nfa wf it current i (Nat.le_of_lt hlt) next = (matched, next') := by
  unfold eachStepChar2.go
  simp [Nat.ne_of_lt hlt, h, found]

@[simp]
theorem eachStepChar.go_not_found {i}
  (hlt : i < current.states.count)
  (h : stepChar2 nfa wf it current.updates next current.states[i] = (matched, next')) (not_found : ¬matched.isSome) :
  eachStepChar2.go nfa wf it current i (Nat.le_of_lt hlt) next = eachStepChar2.go nfa wf it current (i + 1) (by omega) next' := by
  conv =>
    lhs
    unfold eachStepChar2.go
    simp [Nat.ne_of_lt hlt, h, not_found]

@[simp]
theorem captureNext.go_not_found (atEnd : it.atEnd) :
  captureNext2.go nfa wf bufferSize it matched current next = matched := by
  simp [captureNext2.go, atEnd]

@[simp]
theorem captureNext.go_found
  (atEnd : ¬it.atEnd) (isEmpty : current.states.isEmpty) (isSome : matched.isSome) :
  captureNext2.go nfa wf bufferSize it matched current next = matched := by
  simp [captureNext2.go, atEnd, isEmpty, isSome]

@[simp]
theorem captureNext.go_ind_not_found {_matched matched'}
  (atEnd : ¬it.atEnd) (isNone : matched.isNone)
  (h₁ : εClosure2 nfa wf it .none current [(Buffer.empty, ⟨nfa.start, wf.start_lt⟩)] = (_matched, current'))
  (h₂ : eachStepChar2 nfa wf it current' next = (matched', next')) :
  captureNext2.go nfa wf bufferSize it matched current next = captureNext2.go nfa wf bufferSize it.next matched' next' ⟨current.states.clear, current.updates⟩ := by
  have isSome : ¬matched.isSome := by
    cases matched <;> simp_all
  conv =>
    lhs
    unfold captureNext2.go
    simp [atEnd, isSome, isNone, h₁, h₂]

@[simp]
theorem captureNext.go_ind_found {matched'}
  (atEnd : ¬it.atEnd) (isEmpty : ¬current.states.isEmpty) (isSome : matched.isSome)
  (h : eachStepChar2 nfa wf it current next = (matched', next')) :
  captureNext2.go nfa wf bufferSize it matched current next = captureNext2.go nfa wf bufferSize it.next (matched' <|> matched) next' ⟨current.states.clear, current.updates⟩ := by
  have isNone : ¬matched.isNone := by
    cases matched <;> simp_all
  conv =>
    lhs
    unfold captureNext2.go
    simp [atEnd, isEmpty, isSome, isNone, h]

end Regex.VM
