import Regex.Data.SparseSet
import Regex.NFA.Basic
import Regex.Strategy

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

/-
  The following implementation is heavily inspired by burntsushi's regex-lite crate.
  https://github.com/rust-lang/regex/tree/master/regex-lite
-/
namespace Regex.VM

structure SearchState (σ : Strategy) (nfa : NFA) where
  states : SparseSet nfa.nodes.size
  updates : Vector σ.Update nfa.nodes.size

abbrev εStack (σ : Strategy) (nfa : NFA) := List (σ.Update × Fin nfa.nodes.size)

namespace εClosure

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
@[inline]
def writeUpdate (node : NFA.Node) : Bool :=
  match node with
  | .done | .char _ _ | .sparse _ _ => true
  | _ => false

@[inline]
def pushNext (σ : Strategy) (nfa : NFA) (it : Iterator) (node : NFA.Node) (inBounds : node.inBounds nfa.nodes.size) (update : σ.Update) (stack : εStack σ nfa) : εStack σ nfa :=
  match node with
  | .epsilon state' => (update, ⟨state', inBounds⟩) :: stack
  | .split state₁ state₂ => (update, ⟨state₁, inBounds.1⟩) :: (update, ⟨state₂, inBounds.2⟩) :: stack
  | .save offset state' => (σ.write update offset it.pos, ⟨state', inBounds⟩) :: stack
  | .anchor a state' =>
    if a.test it then
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
@[specialize σ] -- TODO: doesn't seem to generate code for BufferStrategy
def εClosure (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (matched : Option σ.Update) (next : SearchState σ nfa) (stack : εStack σ nfa) :
  Option σ.Update × SearchState σ nfa :=
  match stack with
  | [] => (matched, next)
  | (update, state) :: stack' =>
    if mem : state ∈ next.states then
      εClosure σ nfa wf it matched next stack'
    else
      match h : next with
      | ⟨states, updates⟩ =>
        let node := nfa[state]
        let matched' := if node.isDone then matched <|> update else matched
        let states' := states.insert state mem
        let updates' := if εClosure.writeUpdate node then updates.set state update else updates
        let stack'' := εClosure.pushNext σ nfa it node (wf.inBounds state) update stack'
        have : states'.measure < states.measure := SparseSet.lt_measure_insert' mem
        εClosure σ nfa wf it matched' ⟨states', updates'⟩ stack''
termination_by (next.states.measure, stack)

/--
If the given state can make a transition on the current character of `it`, make the transition and
traverse ε-closures from the resulting state.
-/
@[specialize σ]
def stepChar (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (currentUpdates : Vector σ.Update nfa.nodes.size)
  (next : SearchState σ nfa) (state : Fin nfa.nodes.size) :
  Option σ.Update × SearchState σ nfa :=
  let state' : Option (Fin nfa.nodes.size) :=
    match hn : nfa[state] with
    | .char c state' =>
      if it.curr = c then
        .some ⟨state', wf.inBounds' state hn⟩
      else
        .none
    | .sparse cs state' =>
      if it.curr ∈ cs then
        .some ⟨state', wf.inBounds' state hn⟩
      else
        .none
    | _ => .none
  match state' with
  | .some state' =>
    let update := currentUpdates[state]
    εClosure σ nfa wf it.next .none next [(update, state')]
  | .none =>
    (.none, next)

/--
For all states in `current`, make a transition on the current character of `it` and traverse
ε-closures from the resulting states.
-/
@[specialize σ]
def eachStepChar (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (current : SearchState σ nfa) (next : SearchState σ nfa) :
  Option σ.Update × SearchState σ nfa :=
  go 0 (Nat.zero_le _) next
where
  @[specialize σ]
  go (i : Nat) (hle : i ≤ current.states.count) (next : SearchState σ nfa) :
    Option σ.Update × SearchState σ nfa :=
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
        let result := stepChar σ nfa wf it current.updates next state
        if result.1.isSome then
          -- Early-stop iteration when we found a path to `.done` after stepping from `state`
          -- since the path will be prioritized over the paths through the later nodes.
          result
        else
          go (i + 1) hlt result.2

@[specialize σ]
def captureNext (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) : Option σ.Update :=
  let updates : Vector σ.Update nfa.nodes.size := Vector.replicate nfa.nodes.size σ.empty
  let (matched, current) := εClosure σ nfa wf it .none ⟨.empty, updates⟩ [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
  go it matched current ⟨.empty, updates⟩
where
  @[specialize σ]
  go (it : Iterator) (matched : Option σ.Update) (current next : SearchState σ nfa) :
    Option σ.Update :=
    if it.atEnd then
      matched
    else
      if current.states.isEmpty && matched.isSome then
        matched
      else
        let stepped := eachStepChar σ nfa wf it current next
        let matched' := stepped.1 <|> matched
        if matched'.isNone then
          let expanded := εClosure σ nfa wf it.next .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
          go it.next expanded.1 expanded.2 ⟨current.states.clear, current.updates⟩
        else
          go it.next matched' stepped.2 ⟨current.states.clear, current.updates⟩

def captureNextBuf (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (it : Iterator) : Option (Buffer bufferSize) :=
  captureNext (BufferStrategy bufferSize) nfa wf it

end Regex.VM
