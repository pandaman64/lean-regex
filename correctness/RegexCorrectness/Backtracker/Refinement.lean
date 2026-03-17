module

import all RegexCorrectness.Backtracker.Traversal
import all RegexCorrectness.Strategy.Materialize.Basic
import all RegexCorrectness.Strategy.Materialize.Lemmas
import RegexCorrectness.Strategy
import Regex.Strategy

open Regex (NFA)
open Regex.Data (BitMatrix BVPos)
open Regex.Strategy (materializeUpdates materializeUpdates_snoc)
open Regex.PosTracker (listTracker vectorTracker)
open String (Pos PosPlusOne)
namespace Regex.Backtracker

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s} {bufferSize : Nat}

def StackEntry.materialize (entryH : StackEntry (List (Nat × Pos s)) nfa startPos) : StackEntry (Vector (PosPlusOne s) bufferSize) nfa startPos :=
  ⟨materializeUpdates bufferSize entryH.update, entryH.state, entryH.pos⟩

def materializeStack (stackH : List (StackEntry (List (Nat × Pos s)) nfa startPos)) : List (StackEntry (Vector (PosPlusOne s) bufferSize) nfa startPos) :=
  stackH.map StackEntry.materialize

@[simp]
theorem materializeStack.nil : materializeStack [] = ([] : List (StackEntry (Vector (PosPlusOne s) bufferSize) nfa startPos)) := rfl

@[simp]
theorem materializeStack.cons {entryH stackH} :
  materializeStack (entryH :: stackH) = (StackEntry.materialize entryH :: materializeStack stackH : List (StackEntry (Vector (PosPlusOne s) bufferSize) nfa startPos)) := rfl

def materializeResultAux (resultH : Option (List (Nat × Pos s)) × BitMatrix nfa.size (startPos.remainingBytes + 1)) : Option (Vector (PosPlusOne s) bufferSize) × BitMatrix nfa.size (startPos.remainingBytes + 1) :=
  ⟨resultH.1.map (materializeUpdates bufferSize), resultH.2⟩

def materializeResult (resultH : Option (List (Nat × Pos s))) : Option (Vector (PosPlusOne s) bufferSize) :=
  resultH.map (materializeUpdates bufferSize)

theorem captureNextAux.pushNext.refines {s nfa wf startPos bufferSize stackH stackB updateH updateB state pos}
  (refEntry : StackEntry.materialize ⟨updateH, state, pos⟩ = ⟨updateB, state, pos⟩) (refStack : materializeStack stackH = stackB) :
  materializeStack (captureNextAux.pushNext (listTracker s) nfa wf startPos stackH updateH state pos) = captureNextAux.pushNext (vectorTracker s bufferSize) nfa wf startPos stackB updateB state pos := by
  cases stackH, updateH, state, pos using captureNextAux.pushNext.fun_cases' nfa wf startPos with
  | done stackH updateH state pos hn => simp [pushNext.done hn, refStack]
  | fail stackH updateH state pos hn => simp [pushNext.fail hn, refStack]
  | epsilon stackH updateH state pos state' hn =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.epsilon hn, StackEntry.materialize, refStack, refEntry]
  | split stackH updateH state pos state₁ state₂ hn =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.split hn, StackEntry.materialize, refStack, refEntry]
  | save stackH updateH state pos offset state' hn =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.save hn, StackEntry.materialize, refStack, refEntry, listTracker, vectorTracker, materializeUpdates_snoc]
  | anchor_pos stackH updateH state pos a state' hn ht =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.anchor_pos hn ht, StackEntry.materialize, refStack, refEntry]
  | anchor_neg stackH updateH state pos a state' hn ht =>
    simp [pushNext.anchor_neg hn ht, refStack]
  | char_pos stackH updateH state pos c state' hn hnext hc =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.char_pos hn hnext hc, StackEntry.materialize, refStack, refEntry]
  | char_neg stackH updateH state pos c state' hn h =>
    simp [pushNext.char_neg hn h, refStack]
  | sparse_pos stackH updateH state pos cs state' hn hnext hc =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.sparse_pos hn hnext hc, StackEntry.materialize, refStack, refEntry]
  | sparse_neg stackH updateH state pos cs state' hn h =>
    simp [pushNext.sparse_neg hn h, refStack]

theorem captureNextAux.refines {s} (nfa wf startPos bufferSize visited) {stackH stackB} (refStack : materializeStack stackH = stackB) :
  materializeResultAux (captureNextAux (listTracker s) nfa wf startPos visited stackH) = captureNextAux (vectorTracker s bufferSize) nfa wf startPos visited stackB := by
  induction visited, stackH using captureNextAux.induct' (listTracker s) nfa wf startPos generalizing stackB with
  | base visited =>
    simp at refStack
    simp [refStack, captureNextAux_base, materializeResultAux]
  | visited visited update state' pos stackH mem ih =>
    simp at refStack
    simpa [←refStack, StackEntry.materialize, captureNextAux_visited mem] using ih rfl
  | done visited update state' pos stackH mem hn =>
    simp at refStack
    simp [←refStack, StackEntry.materialize, captureNextAux_done mem hn, materializeResultAux]
  | next visited update state' pos stackH mem hn ih =>
    simp at refStack
    simp [←refStack, StackEntry.materialize, captureNextAux_next mem hn]
    exact ih (pushNext.refines rfl rfl)

theorem captureNext.go.refines {s} (nfa wf startPos bufferSize bvpos visited) :
  materializeResult (captureNext.go (listTracker s) nfa wf startPos bvpos visited) = captureNext.go (vectorTracker s bufferSize) nfa wf startPos bvpos visited := by
  induction bvpos, visited using captureNext.go.induct' (List (Nat × Pos s)) (listTracker s) nfa wf startPos with
  | found bvpos visited updateH visitedH hauxH =>
    have hauxB := captureNextAux.refines nfa wf startPos bufferSize visited rfl (stackB := materializeStack [⟨(listTracker s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩])
    simp [↓hauxH, materializeResultAux] at hauxB
    simp [captureNext.go_found hauxH, captureNext.go_found hauxB.symm, materializeResult]
  | not_found_next bvpos visited visitedH hauxH ne ih =>
    have hauxB := captureNextAux.refines nfa wf startPos bufferSize visited rfl (stackB := materializeStack [⟨(listTracker s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩])
    simp [↓hauxH, materializeResultAux] at hauxB
    simpa [captureNext.go_not_found_next hauxH ne, captureNext.go_not_found_next hauxB.symm ne] using ih
  | not_found_end bvpos visited visitedH hauxH ne =>
    have hauxB := captureNextAux.refines nfa wf startPos bufferSize visited rfl (stackB := materializeStack [⟨(listTracker s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩])
    simp [↓hauxH, materializeResultAux] at hauxB
    simp [captureNext.go_not_found_end hauxH ne, captureNext.go_not_found_end hauxB.symm ne, materializeResult]

theorem captureNext.refines {s} (nfa wf bufferSize pos) :
  materializeResult (captureNext (listTracker s) nfa wf pos) = captureNext (vectorTracker s bufferSize) nfa wf pos := by
  simpa [captureNext] using captureNext.go.refines nfa wf pos bufferSize (BVPos.start pos) (BitMatrix.zero _ _)

end Regex.Backtracker
