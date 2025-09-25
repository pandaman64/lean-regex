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

end εClosure

structure εClosureExploreResult (σ : Strategy) (nfa : NFA) where
  matched : Option σ.Update
  states : SparseSet nfa.nodes.size
  updates : Vector σ.Update nfa.nodes.size
  stack : εStack σ nfa

def εClosureExplore (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (matched : Option σ.Update) (states : SparseSet nfa.nodes.size) (updates : Vector σ.Update nfa.nodes.size)
  (update : σ.Update) (state : Fin nfa.nodes.size) (stack : εStack σ nfa) :
  εClosureExploreResult σ nfa :=
  if mem : state ∈ states then
    ⟨matched, states, updates, stack⟩
  else
    let node := nfa[state]
    let matched' := if node.isDone then matched <|> update else matched
    let states' := states.insert state mem
    let updates' := if εClosure.writeUpdate node then updates.set state update else updates
    have : states'.measure < states.measure := SparseSet.lt_measure_insert' mem
    match hn : node with
    | .epsilon state' => εClosureExplore σ nfa wf it matched' states' updates' update ⟨state', wf.inBounds' state hn⟩ stack
    | .split state₁ state₂ => εClosureExplore σ nfa wf it matched' states' updates' update ⟨state₁, (wf.inBounds' state hn).1⟩ ((update, ⟨state₂, (wf.inBounds' state hn).2⟩) :: stack)
    | .save offset state' => εClosureExplore σ nfa wf it matched' states' updates' (σ.write update offset it.pos) ⟨state', wf.inBounds' state hn⟩ stack
    | .anchor a state' =>
      if a.test it then
        εClosureExplore σ nfa wf it matched' states' updates' update ⟨state', wf.inBounds' state hn⟩ stack
      else
        ⟨matched', states', updates', stack⟩
    | .done => ⟨matched', states', updates', stack⟩
    | .fail => ⟨matched', states', updates', stack⟩
    | .char _ _ => ⟨matched', states', updates', stack⟩
    | .sparse _ _ => ⟨matched', states', updates', stack⟩
termination_by states.measure

structure εClosureResult (σ : Strategy) (nfa : NFA) where
  matched : Option σ.Update
  states : SparseSet nfa.nodes.size
  updates : Vector σ.Update nfa.nodes.size

instance {σ : Strategy} {nfa : NFA} : Inhabited (εClosureResult σ nfa) := ⟨⟨.none, .empty, .replicate _ σ.empty⟩⟩

/--
Visit all ε-transitions from the states in the stack, updating `next.states` when the new state is
`.done`, `.char`, or `.sparse`. Returns `.some updates` if a `.done` state is reached, meaning a
match is found.
-/
-- Once we have the new compiler, we may want to test specialization by `@[specialize σ]`.
partial def εClosure (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (matched : Option σ.Update) (states : SparseSet nfa.nodes.size) (updates : Vector σ.Update nfa.nodes.size) (stack : εStack σ nfa) :
  εClosureResult σ nfa :=
  match stack with
  | [] => ⟨matched, states, updates⟩
  | (update, state) :: stack' =>
    let ⟨matched', states', updates', stack''⟩ := εClosureExplore σ nfa wf it matched states updates update state stack'
    -- TODO: prove that `(state ∈ states → states' = states ∧ stack' < stack) ∧ (state ∉ states → states'.measure < states.measure)`
    -- Probably it's easier to handle termination if we assume `state ∉ states` in εClosureExplore.
    εClosure σ nfa wf it matched' states' updates' stack''

/--
If the given state can make a transition on the current character of `it`, make the transition and
traverse ε-closures from the resulting state.
-/
def stepChar (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (currentUpdates : Vector σ.Update nfa.nodes.size)
  (states : SparseSet nfa.nodes.size) (updates : Vector σ.Update nfa.nodes.size) (state : Fin nfa.nodes.size) :
  εClosureResult σ nfa :=
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
    εClosure σ nfa wf it.next .none states updates [(update, state')]
  | .none =>
    ⟨.none, states, updates⟩

/--
For all states in `current`, make a transition on the current character of `it` and traverse
ε-closures from the resulting states.
-/
def eachStepChar (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (currentStates : SparseSet nfa.nodes.size) (currentUpdates : Vector σ.Update nfa.nodes.size)
  (nextStates : SparseSet nfa.nodes.size) (nextUpdates : Vector σ.Update nfa.nodes.size) :
  εClosureResult σ nfa :=
  go 0 (Nat.zero_le _) nextStates nextUpdates
where
  go (i : Nat) (hle : i ≤ currentStates.count) (nextStates : SparseSet nfa.nodes.size) (nextUpdates : Vector σ.Update nfa.nodes.size) :
    εClosureResult σ nfa :=
    if h : i = currentStates.count then
      ⟨.none, nextStates, nextUpdates⟩
    else
      have hlt : i < currentStates.count := Nat.lt_of_le_of_ne hle h
      let state := currentStates[i]
      if nfa[state].isDone then
        -- Early-stop iteration when we encounter `.done` since the path to this `.done` node
        -- is prioritized over the paths through the later nodes.
        ⟨.none, nextStates, nextUpdates⟩
      else
        match stepChar σ nfa wf it currentUpdates nextStates nextUpdates state with
        | ⟨matched, nextStates', nextUpdates'⟩ =>
          if matched.isSome then
            -- Early-stop iteration when we found a path to `.done` after stepping from `state`
            -- since the path will be prioritized over the paths through the later nodes.
            ⟨matched, nextStates', nextUpdates'⟩
          else
            go (i + 1) hlt nextStates' nextUpdates'

def captureNext (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) : Option σ.Update :=
  let updates : Vector σ.Update nfa.nodes.size := Vector.replicate nfa.nodes.size σ.empty
  let ⟨matched, currentStates, currentUpdates⟩ := εClosure σ nfa wf it .none .empty updates [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
  go it matched currentStates currentUpdates .empty updates
where
  go (it : Iterator) (matched : Option σ.Update)
    (currentStates : SparseSet nfa.nodes.size) (currentUpdates : Vector σ.Update nfa.nodes.size)
    (nextStates : SparseSet nfa.nodes.size) (nextUpdates : Vector σ.Update nfa.nodes.size) :
    Option σ.Update :=
    if it.atEnd then
      matched
    else
      if currentStates.isEmpty && matched.isSome then
        matched
      else
        let stepped := eachStepChar σ nfa wf it currentStates currentUpdates nextStates nextUpdates
        let matched' := stepped.matched <|> matched
        if matched'.isNone then
          let expanded := εClosure σ nfa wf it.next .none stepped.states stepped.updates [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
          go it.next expanded.matched expanded.states expanded.updates currentStates.clear currentUpdates
        else
          go it.next matched' stepped.states stepped.updates currentStates.clear currentUpdates

def captureNextBuf (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (it : Iterator) : Option (Buffer bufferSize) :=
  captureNext (BufferStrategy bufferSize) nfa wf it

end Regex.VM
