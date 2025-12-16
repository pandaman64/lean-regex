import Regex.Data.BitMatrix
import Regex.Data.BVPos
import Regex.NFA
import Regex.Strategy

open String (Pos)
open Regex.Data (BitMatrix BVPos)

set_option autoImplicit false

namespace Regex.Backtracker

structure StackEntry {s : String} (σ : Strategy s) (nfa : NFA) (startPos : Pos s) where
  update : σ.Update
  state : Fin nfa.nodes.size
  pos : BVPos startPos

def captureNextAux.pushNext {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s) (stack : List (StackEntry σ nfa startPos))
  (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) :
  List (StackEntry σ nfa startPos) :=
  match hn : nfa[state] with
  | .done => stack
  | .fail => stack
  | .epsilon state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    ⟨update, ⟨state', isLt⟩, pos⟩ :: stack
  | .split state₁ state₂ =>
    have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
    ⟨update, ⟨state₁, isLt.1⟩, pos⟩ :: ⟨update, ⟨state₂, isLt.2⟩, pos⟩ :: stack
  | .save offset state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    let update' := σ.write update offset pos.current
    ⟨update', ⟨state', isLt⟩, pos⟩ :: stack
  | .anchor a state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    if a.test pos.current then
      ⟨update, ⟨state', isLt⟩, pos⟩ :: stack
    else
      stack
  | .char c state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    if h : ∃ h : pos ≠ s.endBVPos startPos, pos.get h = c then
      ⟨update, ⟨state', isLt⟩, pos.next h.1⟩ :: stack
    else
      stack
  | .sparse cs state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    if h : ∃ h : pos ≠ s.endBVPos startPos, pos.get h ∈ cs then
      ⟨update, ⟨state', isLt⟩, pos.next h.1⟩ :: stack
    else
      stack

def captureNextAux {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s)
  (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (stack : List (StackEntry σ nfa startPos)) :
  (Option σ.Update × BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) :=
  match stack with
  | [] => (.none, visited)
  | ⟨update, state, pos⟩ :: stack' =>
    if h : visited.get state pos.index then
      captureNextAux σ nfa wf startPos visited stack'
    else
      let visited' := visited.set state pos.index
      have : nfa.nodes.size * (startPos.remainingBytes + 1) + 1 - visited'.popcount < nfa.nodes.size * (startPos.remainingBytes + 1) + 1 - visited.popcount :=
        BitMatrix.popcount_decreasing visited state pos.index h
      if nfa[state].isDone then
        (.some update, visited')
      else
        let stack'' := captureNextAux.pushNext σ nfa wf startPos stack' update state pos
        captureNextAux σ nfa wf startPos visited' stack''
termination_by (nfa.nodes.size * (startPos.remainingBytes + 1) + 1 - visited.popcount, stack)

def captureNext {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s) : Option σ.Update :=
  go (BVPos.start startPos) (BitMatrix.zero _ _)
where
  go (pos : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) : Option σ.Update :=
  match captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] with
  | (.some update, _) => .some update
  | (.none, visited') =>
    if h : pos ≠ s.endBVPos startPos then
      go (pos.next h) visited'
    else
      .none
  termination_by pos

def captureNextBuf {s : String} (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (p : Pos s) : Option (Buffer s bufferSize) :=
  captureNext (BufferStrategy s bufferSize) nfa wf p

end Regex.Backtracker
