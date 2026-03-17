module

import Regex.Data.SparseSet
public import Regex.NFA.Basic
public import Regex.Strategy
-- Needed to specialize α and tracker for some reason
public import Regex.Data.SparseSet.Basic

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos PosPlusOne)

/-
  The following implementation is heavily inspired by burntsushi's regex-lite crate.
  https://github.com/rust-lang/regex/tree/master/regex-lite
-/
namespace Regex.VM

structure SearchState (α : Type) (nfa : NFA) where
  states : SparseSet nfa.size
  updates : Vector α nfa.size

abbrev εStack (α : Type) (nfa : NFA) := List (α × Fin nfa.size)

namespace εClosure

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
@[inline]
def writeUpdate (node : NFA.Node) : Bool :=
  match node with
  | .done | .char _ _ | .sparse _ _ => true
  | _ => false

@[inline, specialize α, specialize tracker]
def pushNext {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (p : Pos s) (node : NFA.Node) (inBounds : node.inBounds nfa.size) (update : α) (stack : εStack α nfa) : εStack α nfa :=
  match node with
  | .epsilon state' => (update, ⟨state', inBounds⟩) :: stack
  | .split state₁ state₂ => (update, ⟨state₁, inBounds.1⟩) :: (update, ⟨state₂, inBounds.2⟩) :: stack
  | .save offset state' => (tracker.write update offset p, ⟨state', inBounds⟩) :: stack
  | .anchor a state' =>
    if a.test p then
      (update, ⟨state', inBounds⟩) :: stack
    else
      stack
  | .done => stack
  | .fail => stack
  | .char _ _ => stack
  | .sparse _ _ => stack

end εClosure

/--
Visit all ε-transitions from the states in the stack, updating `next.states` when the new state is
`.done`, `.char`, or `.sparse`. Returns `.some updates` if a `.done` state is reached, meaning a
match is found.
-/
-- Once we have the new compiler, we may want to test specialization by `@[specialize σ]`.
@[specialize α, specialize tracker]
def εClosure {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (p : Pos s)
  (matched : Option α) (next : SearchState α nfa) (stack : εStack α nfa) :
  Option α × SearchState α nfa :=
  match stack with
  | [] => (matched, next)
  | (update, state) :: stack' =>
    if mem : state ∈ next.states then
      εClosure tracker nfa wf p matched next stack'
    else
      match h : next with
      | ⟨states, updates⟩ =>
        let node := nfa[state]
        let matched' := if node.isDone then matched <|> update else matched
        let states' := states.insert state mem
        let updates' := if εClosure.writeUpdate node then updates.set state update else updates
        let stack'' := εClosure.pushNext tracker nfa p node (wf.inBounds state state.isLt) update stack'
        have : states'.measure < states.measure := SparseSet.lt_measure_insert' mem
        εClosure tracker nfa wf p matched' ⟨states', updates'⟩ stack''
termination_by (next.states.measure, stack)

/--
If the given state can make a transition on the current character of `it`, make the transition and
traverse ε-closures from the resulting state.
-/
@[specialize α, specialize tracker]
def stepChar {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (p : Pos s) (ne : p ≠ s.endPos) (currentUpdates : Vector α nfa.size)
  (next : SearchState α nfa) (state : Fin nfa.size) :
  Option α × SearchState α nfa :=
  let state' : Option (Fin nfa.size) :=
    match hn : nfa[state] with
    | .char c state' =>
      if p.get ne = c then
        .some ⟨state', wf.inBounds' state state.isLt hn⟩
      else
        .none
    | .sparse cs state' =>
      if p.get ne ∈ cs then
        .some ⟨state', wf.inBounds' state state.isLt hn⟩
      else
        .none
    | _ => .none
  match state' with
  | .some state' =>
    let update := currentUpdates[state]
    εClosure tracker nfa wf (p.next ne) .none next [(update, state')]
  | .none =>
    (.none, next)

/--
For all states in `current`, make a transition on the current character of `it` and traverse
ε-closures from the resulting states.
-/
@[specialize α, specialize tracker]
def eachStepChar {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (p : Pos s) (ne : p ≠ s.endPos)
  (current : SearchState α nfa) (next : SearchState α nfa) :
  Option α × SearchState α nfa :=
  go 0 (Nat.zero_le _) next
where
  go (i : Nat) (hle : i ≤ current.states.count) (next : SearchState α nfa) :
    Option α × SearchState α nfa :=
    if h : i = current.states.count then
      (.none, next)
    else
      have hlt : i < current.states.count := Nat.lt_of_le_of_ne hle h
      let state := current.states[i]
      if nfa[state].isDone then
        -- Early-stop iteration when we encounter `.done` since the path to this `.done` node
        -- is prioritized over the paths through the later nodes.
        (.none, next)
      else
        let result := stepChar tracker nfa wf p ne current.updates next state
        if result.1.isSome then
          -- Early-stop iteration when we found a path to `.done` after stepping from `state`
          -- since the path will be prioritized over the paths through the later nodes.
          result
        else
          go (i + 1) hlt result.2

@[specialize α, specialize tracker]
public def captureNext {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (p : Pos s) : Option α :=
  let updates : Vector α nfa.size := Vector.replicate nfa.size tracker.empty
  let (matched, current) := εClosure tracker nfa wf p .none ⟨.empty, updates⟩ [(tracker.empty, ⟨nfa.start, wf.start_lt⟩)]
  go p matched current ⟨.empty, updates⟩
where
  @[specialize α, specialize tracker]
  go (p : Pos s) (matched : Option α) (current next : SearchState α nfa) :
    Option α :=
    if h : p = s.endPos then
      matched
    else
      if current.states.isEmpty && matched.isSome then
        matched
      else
        let stepped := eachStepChar tracker nfa wf p h current next
        let matched' := stepped.1 <|> matched
        if matched'.isNone then
          let expanded := εClosure tracker nfa wf (p.next h) .none stepped.2 [(tracker.empty, ⟨nfa.start, wf.start_lt⟩)]
          go (p.next h) expanded.1 expanded.2 ⟨current.states.clear, current.updates⟩
        else
          go (p.next h) matched' stepped.2 ⟨current.states.clear, current.updates⟩
  termination_by p

public def captureNextBuf {s : String} (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (p : Pos s) : Option (Vector (PosPlusOne s) bufferSize) :=
  captureNext inferInstance nfa wf p

end Regex.VM
