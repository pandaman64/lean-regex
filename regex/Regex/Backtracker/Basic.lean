module

public import Regex.Data.BitMatrix
public import Regex.Data.BVPos
public import Regex.NFA
public import Regex.Strategy

open String (Pos PosPlusOne)
open Regex.Data (BitMatrix BVPos)

namespace Regex.Backtracker

structure StackEntry {s : String} (α : Type) (nfa : NFA) (startPos : Pos s) where
  update : α
  state : Fin nfa.size
  pos : BVPos startPos

@[specialize α, specialize tracker]
def captureNextAux.pushNext {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s) (stack : List (StackEntry α nfa startPos))
  (update : α) (state : Fin nfa.size) (pos : BVPos startPos) :
  List (StackEntry α nfa startPos) :=
  match hn : nfa[state] with
  | .done => stack
  | .fail => stack
  | .epsilon state' =>
    have isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
    ⟨update, ⟨state', isLt⟩, pos⟩ :: stack
  | .split state₁ state₂ =>
    have isLt : state₁ < nfa.size ∧ state₂ < nfa.size := wf.inBounds' state state.isLt hn
    ⟨update, ⟨state₁, isLt.1⟩, pos⟩ :: ⟨update, ⟨state₂, isLt.2⟩, pos⟩ :: stack
  | .save offset state' =>
    have isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
    let update' := tracker.write update offset pos.current
    ⟨update', ⟨state', isLt⟩, pos⟩ :: stack
  | .anchor a state' =>
    have isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
    if a.test pos.current then
      ⟨update, ⟨state', isLt⟩, pos⟩ :: stack
    else
      stack
  | .char c state' =>
    have isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
    if h : ∃ h : pos ≠ s.endBVPos startPos, pos.get h = c then
      ⟨update, ⟨state', isLt⟩, pos.next h.1⟩ :: stack
    else
      stack
  | .sparse cs state' =>
    have isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
    if h : ∃ h : pos ≠ s.endBVPos startPos, pos.get h ∈ cs then
      ⟨update, ⟨state', isLt⟩, pos.next h.1⟩ :: stack
    else
      stack

@[specialize α, specialize tracker]
def captureNextAux {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s)
  (visited : BitMatrix nfa.size (startPos.remainingBytes + 1)) (stack : List (StackEntry α nfa startPos)) :
  (Option α × BitMatrix nfa.size (startPos.remainingBytes + 1)) :=
  match stack with
  | [] => (.none, visited)
  | ⟨update, state, pos⟩ :: stack' =>
    if h : visited.get state pos.index then
      captureNextAux tracker nfa wf startPos visited stack'
    else
      let visited' := visited.set state pos.index
      have : nfa.size * (startPos.remainingBytes + 1) + 1 - visited'.popcount < nfa.size * (startPos.remainingBytes + 1) + 1 - visited.popcount :=
        BitMatrix.popcount_decreasing visited state pos.index h
      if nfa[state].isDone then
        (.some update, visited')
      else
        let stack'' := captureNextAux.pushNext tracker nfa wf startPos stack' update state pos
        captureNextAux tracker nfa wf startPos visited' stack''
termination_by (nfa.size * (startPos.remainingBytes + 1) + 1 - visited.popcount, stack)

@[specialize α, specialize tracker]
public def captureNext {α : Type} {s : String} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s) : Option α :=
  go (BVPos.start startPos) (BitMatrix.zero _ _)
where
  @[specialize α, specialize tracker]
  go (pos : BVPos startPos) (visited : BitMatrix nfa.size (startPos.remainingBytes + 1)) : Option α :=
  match captureNextAux tracker nfa wf startPos visited [⟨tracker.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] with
  | (.some update, _) => .some update
  | (.none, visited') =>
    if h : pos ≠ s.endBVPos startPos then
      go (pos.next h) visited'
    else
      .none
  termination_by pos

public def captureNextBuf {s : String} (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (p : Pos s) : Option (Vector (PosPlusOne s) bufferSize) :=
  captureNext inferInstance nfa wf p

end Regex.Backtracker
