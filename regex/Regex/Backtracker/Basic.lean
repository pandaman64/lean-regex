import Regex.Data.BitMatrix
import Regex.Data.BoundedIterator
import Regex.NFA
import Regex.Strategy

open String (Iterator Pos)
open Regex.Data (BitMatrix BoundedIterator)

set_option autoImplicit false

namespace Regex.Backtracker

structure StackEntry (σ : Strategy) (nfa : NFA) (startIdx maxIdx : Nat) where
  update : σ.Update
  state : Fin nfa.nodes.size
  it : BoundedIterator startIdx maxIdx

def captureNextAux.pushNext (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx maxIdx : Nat) (stack : List (StackEntry σ nfa startIdx maxIdx))
  (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) :
  List (StackEntry σ nfa startIdx maxIdx) :=
  match hn : nfa[state] with
  | .done => stack
  | .fail => stack
  | .epsilon state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    ⟨update, ⟨state', isLt⟩, it⟩ :: stack
  | .split state₁ state₂ =>
    have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
    ⟨update, ⟨state₁, isLt.1⟩, it⟩ :: ⟨update, ⟨state₂, isLt.2⟩, it⟩ :: stack
  | .save offset state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    let update' := σ.write update offset it.pos
    ⟨update', ⟨state', isLt⟩, it⟩ :: stack
  | .anchor a state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    if a.test it.it then
      ⟨update, ⟨state', isLt⟩, it⟩ :: stack
    else
      stack
  | .char c state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    if h : ∃ hnext : it.hasNext, it.curr hnext = c then
      ⟨update, ⟨state', isLt⟩, it.next h.1⟩ :: stack
    else
      stack
  | .sparse cs state' =>
    have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
    if h : ∃ hnext : it.hasNext, it.curr hnext ∈ cs then
      ⟨update, ⟨state', isLt⟩, it.next h.1⟩ :: stack
    else
      stack

def captureNextAux (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx maxIdx : Nat)
  (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (stack : List (StackEntry σ nfa startIdx maxIdx)) :
  (Option σ.Update × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) :=
  match stack with
  | [] => (.none, visited)
  | ⟨update, state, it⟩ :: stack' =>
    if h : visited.get state it.index then
      captureNextAux σ nfa wf startIdx maxIdx visited stack'
    else
      let visited' := visited.set state it.index
      have : nfa.nodes.size * (maxIdx + 1 - startIdx) + 1 - visited'.popcount < nfa.nodes.size * (maxIdx + 1 - startIdx) + 1 - visited.popcount :=
        BitMatrix.popcount_decreasing visited state it.index h
      if nfa[state] = .done then
        (.some update, visited')
      else
        let stack'' := captureNextAux.pushNext σ nfa wf startIdx maxIdx stack' update state it
        captureNextAux σ nfa wf startIdx maxIdx visited' stack''
termination_by (nfa.nodes.size * (maxIdx + 1 - startIdx) + 1 - visited.popcount, stack)

def captureNext (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) : Option σ.Update :=
  let startIdx := it.pos.byteIdx
  let maxIdx := it.toString.endPos.byteIdx
  if le : it.pos ≤ it.toString.endPos then
    let bit : BoundedIterator startIdx maxIdx := ⟨it, Nat.le_refl _, le, rfl⟩
    (go startIdx maxIdx bit (BitMatrix.zero _ _)).1
  else
    .none
where
  -- TODO: we don't need to return the visited matrix, but we need to restate the theorems to directly derive the result
  -- rather than describing the returned visited matrix.
  go (startIdx maxIdx : Nat) (bit : BoundedIterator startIdx maxIdx) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) :
  Option σ.Update × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx) :=
  match captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] with
  | (.some update, visited') => (.some update, visited')
  | (.none, visited') =>
    if h : bit.hasNext then
      have : (bit.next h).remainingBytes < bit.remainingBytes := bit.next_remainingBytes_lt h
      go startIdx maxIdx (bit.next h) visited'
    else
      (.none, visited')
  termination_by bit.remainingBytes

def captureNextBuf (nfa : NFA) (wf : nfa.WellFormed) (bufferSize : Nat) (it : Iterator) : Option (Buffer bufferSize) :=
  captureNext (BufferStrategy bufferSize) nfa wf it

end Regex.Backtracker
