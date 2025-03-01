import Regex.Data.SparseSet
import Regex.NFA.Basic
import Regex.VM.Strategy

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

/-
  The following implementation is heavily inspired by burntsushi's regex-lite crate.
  https://github.com/rust-lang/regex/tree/master/regex-lite
-/
namespace Regex.VM

/--
Visit all ε-transitions from the states in the stack, updating `next.states` when the new state is
`.done`, `.char`, or `.sparse`. Returns `.some updates` if a `.done` state is reached, meaning a
match is found.
-/
@[specialize]
def εClosure [σ : Strategy] (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (matched : Option σ.Update) (next : SearchState nfa) (stack : εStack nfa) :
  Option σ.Update × SearchState nfa :=
  match stack with
  | [] => (matched, next)
  | (update, state) :: stack' =>
    if state ∈ next.states then
      εClosure nfa wf it matched next stack'
    else
      match h : next with
      | ⟨states, updates⟩ =>
        let states' := states.insert state
        match hn : nfa[state] with
        | .epsilon state' =>
          have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
          εClosure nfa wf it matched ⟨states', updates⟩ ((update, ⟨state', isLt⟩) :: stack')
        | .anchor a state' =>
          have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
          if a.test it then
            εClosure nfa wf it matched ⟨states', updates⟩ ((update, ⟨state', isLt⟩) :: stack')
          else
            εClosure nfa wf it matched ⟨states', updates⟩ stack'
        | .split state₁ state₂ =>
          have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
          εClosure nfa wf it matched ⟨states', updates⟩ ((update, ⟨state₁, isLt.1⟩) :: (update, ⟨state₂, isLt.2⟩):: stack')
        | .save offset state' =>
          have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
          -- Write the position only when `offset` is in bounds.
          let update' := σ.set update offset it.pos
          εClosure nfa wf it matched ⟨states', updates⟩ ((update', ⟨state', isLt⟩) :: stack')
        | .done =>
          let matched' := matched <|> update
          let updates' := updates.set state update
          εClosure nfa wf it matched' ⟨states', updates'⟩ stack'
        | .char c state' =>
          let updates' := updates.set state update
          εClosure nfa wf it matched ⟨states', updates'⟩ stack'
        | .sparse cs state' =>
          let updates' := updates.set state update
          εClosure nfa wf it matched ⟨states', updates'⟩ stack'
        | .fail => εClosure nfa wf it matched ⟨states', updates⟩ stack'
termination_by (next.states.measure, stack)

/--
If the given state can make a transition on the current character of `it`, make the transition and
traverse ε-closures from the resulting state.
-/
@[specialize]
def stepChar [σ : Strategy] (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (currentUpdates : Vector σ.Update nfa.nodes.size)
  (next : SearchState nfa) (state : Fin nfa.nodes.size) :
  Option σ.Update × SearchState nfa :=
  match hn : nfa[state] with
  | .char c state' =>
    if it.curr = c then
      have isLt := wf.inBounds' state hn
      let update := currentUpdates.get state
      εClosure nfa wf it.next .none next [(update, ⟨state', isLt⟩)]
    else
      (.none, next)
  | .sparse cs state' =>
    if it.curr ∈ cs then
      have isLt := wf.inBounds' state hn
      let update := currentUpdates.get state
      εClosure nfa wf it.next .none next [(update, ⟨state', isLt⟩)]
    else
      (.none, next)
  | _ => (.none, next)

/--
For all states in `current`, make a transition on the current character of `it` and traverse
ε-closures from the resulting states.
-/
@[specialize]
def eachStepChar [σ : Strategy] (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (current : SearchState nfa) (next : SearchState nfa) :
  Option σ.Update × SearchState nfa :=
  go 0 (Nat.zero_le _) next
where
  @[specialize]
  go (i : Nat) (hle : i ≤ current.states.count) (next : SearchState nfa) :
    Option σ.Update × SearchState nfa :=
    if h : i = current.states.count then
      (none, next)
    else
      have hlt : i < current.states.count := Nat.lt_of_le_of_ne hle h
      let result := stepChar nfa wf it current.updates next current.states[i]
      if result.1.isSome then
        result
      else
        go (i + 1) hlt result.2

@[specialize]
def captureNext [σ : Strategy] (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) : Option σ.Update :=
  let updates : Vector σ.Update nfa.nodes.size := Vector.mkVector nfa.nodes.size σ.empty
  let (matched, current) := εClosure nfa wf it .none ⟨.empty, updates⟩ [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
  go it matched current ⟨.empty, updates⟩
where
  @[specialize]
  go (it : Iterator) (matched : Option σ.Update) (current next : SearchState nfa) :
    Option σ.Update :=
    if it.atEnd then
      matched
    else
      if current.states.isEmpty && matched.isSome then
        matched
      else
        if matched.isNone then
          let expanded := εClosure nfa wf it none current [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
          let stepped := eachStepChar nfa wf it expanded.2 next
          go it.next stepped.1 stepped.2 ⟨expanded.2.states.clear, expanded.2.updates⟩
        else
          let stepped := eachStepChar nfa wf it current next
          go it.next (stepped.1 <|> matched) stepped.2 ⟨current.states.clear, current.updates⟩

def captureNextBuf (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (it : Iterator) : Option (Buffer bufferSize) :=
  let _ := BufferStrategy bufferSize
  captureNext nfa wf it

def searchNext (nfa : NFA) (wf : nfa.WellFormed) (it : String.Iterator) : Option (Pos × Pos) := do
  let slots ← captureNextBuf nfa wf 2 it
  pure (← slots[0], ← slots[1])

end Regex.VM
