import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.Strategy

set_option autoImplicit false

open Regex (NFA)
open Regex.Data (BitMatrix BoundedIterator)
open Regex.Strategy (materializeUpdates)
open String (Pos)
namespace Regex.Backtracker

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx bufferSize : Nat}

def StackEntry.materialize (entryH : StackEntry HistoryStrategy nfa startIdx maxIdx) : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx :=
  ⟨materializeUpdates bufferSize entryH.update, entryH.state, entryH.it⟩

def materializeStack (stackH : List (StackEntry HistoryStrategy nfa startIdx maxIdx)) : List (StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx) :=
  stackH.map StackEntry.materialize

@[simp]
theorem materializeStack.nil : materializeStack [] = ([] : List (StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx)) := rfl

@[simp]
theorem materializeStack.cons {entryH stackH} :
  materializeStack (entryH :: stackH) = (StackEntry.materialize entryH :: materializeStack stackH : List (StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx)) := rfl

def materializeResultAux (resultH : Option (List (Nat × Pos)) × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Option (Buffer bufferSize) × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx) :=
  ⟨resultH.1.map (materializeUpdates bufferSize), resultH.2⟩

def materializeResult (resultH : Option (List (Nat × Pos))) : Option (Buffer bufferSize) :=
  resultH.map (materializeUpdates bufferSize)

theorem captureNextAux.pushNext.refines {nfa wf startIdx maxIdx bufferSize stackH stackB updateH updateB state it}
  (refEntry : StackEntry.materialize ⟨updateH, state, it⟩ = ⟨updateB, state, it⟩) (refStack : materializeStack stackH = stackB) :
  materializeStack (captureNextAux.pushNext HistoryStrategy nfa wf startIdx maxIdx stackH updateH state it) = captureNextAux.pushNext (BufferStrategy bufferSize) nfa wf startIdx maxIdx stackB updateB state it := by
  cases stackH, updateH, state, it using captureNextAux.pushNext.fun_cases' HistoryStrategy nfa wf startIdx maxIdx with
  | done stackH updateH state it hn => simp [pushNext.done hn, refStack]
  | fail stackH updateH state it hn => simp [pushNext.fail hn, refStack]
  | epsilon stackH updateH state it state' hn =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.epsilon hn, StackEntry.materialize, refStack, refEntry]
  | split stackH updateH state it state₁ state₂ hn =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.split hn, StackEntry.materialize, refStack, refEntry]
  | save stackH updateH state it offset state' hn =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.save hn, StackEntry.materialize, refStack, refEntry]
  | anchor_pos stackH updateH state it a state' hn ht =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.anchor_pos hn ht, StackEntry.materialize, refStack, refEntry]
  | anchor_neg stackH updateH state it a state' hn ht =>
    simp [pushNext.anchor_neg hn ht, refStack]
  | char_pos stackH updateH state it c state' hn hnext hc =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.char_pos hn hnext hc, StackEntry.materialize, refStack, refEntry]
  | char_neg stackH updateH state it c state' hn h =>
    simp [pushNext.char_neg hn h, refStack]
  | sparse_pos stackH updateH state it cs state' hn hnext hc =>
    simp [StackEntry.materialize] at refEntry
    simp [pushNext.sparse_pos hn hnext hc, StackEntry.materialize, refStack, refEntry]
  | sparse_neg stackH updateH state it cs state' hn h =>
    simp [pushNext.sparse_neg hn h, refStack]

theorem captureNextAux.refines (nfa wf startIdx maxIdx bufferSize visited) {stackH stackB} (refStack : materializeStack stackH = stackB) :
  materializeResultAux (captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stackH) = captureNextAux (BufferStrategy bufferSize) nfa wf startIdx maxIdx visited stackB := by
  induction visited, stackH using captureNextAux.induct' HistoryStrategy nfa wf startIdx maxIdx generalizing stackB with
  | base visited =>
    simp at refStack
    simp [refStack, captureNextAux_base, materializeResultAux]
  | visited visited update state' it stackH mem ih =>
    simp at refStack
    simpa [←refStack, StackEntry.materialize, captureNextAux_visited mem] using ih rfl
  | done visited update state' it stackH mem hn =>
    simp at refStack
    simp [←refStack, StackEntry.materialize, captureNextAux_done mem hn, materializeResultAux]
  | next visited update state' it stackH mem hn ih =>
    simp at refStack
    simp [←refStack, StackEntry.materialize, captureNextAux_next mem hn]
    exact ih (pushNext.refines rfl rfl)

theorem captureNext.go.refines (nfa wf startIdx bufferSize bit visited) :
  materializeResult (captureNext.go HistoryStrategy nfa wf startIdx maxIdx bit visited) = captureNext.go (BufferStrategy bufferSize) nfa wf startIdx maxIdx bit visited := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | found bit visited updateH visitedH hauxH =>
    have hauxB := captureNextAux.refines nfa wf startIdx maxIdx bufferSize visited rfl (stackB := materializeStack [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩])
    simp [↓hauxH, materializeResultAux] at hauxB
    simp [captureNext.go_found hauxH, captureNext.go_found hauxB.symm, materializeResult]
  | not_found_next bit visited visitedH hauxH hnext ih =>
    have hauxB := captureNextAux.refines nfa wf startIdx maxIdx bufferSize visited rfl (stackB := materializeStack [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩])
    simp [↓hauxH, materializeResultAux] at hauxB
    simpa [captureNext.go_not_found_next hauxH hnext, captureNext.go_not_found_next hauxB.symm hnext] using ih
  | not_found_end bit visited visitedH hauxH hnext =>
    have hauxB := captureNextAux.refines nfa wf startIdx maxIdx bufferSize visited rfl (stackB := materializeStack [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩])
    simp [↓hauxH, materializeResultAux] at hauxB
    simp [captureNext.go_not_found_end hauxH hnext, captureNext.go_not_found_end hauxB.symm hnext, materializeResult]

theorem captureNext.refines (nfa wf bufferSize it) :
  materializeResult (captureNext HistoryStrategy nfa wf it) = captureNext (BufferStrategy bufferSize) nfa wf it := by
  if le : it.pos ≤ it.toString.endPos then
    simpa [captureNext_le le] using captureNext.go.refines nfa wf it.pos.byteIdx bufferSize ⟨it, Nat.le_refl _, le, rfl⟩ (BitMatrix.zero _ _)
  else
    simp [captureNext_not_le le, materializeResult]

end Regex.Backtracker
