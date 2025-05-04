import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.Strategy

set_option autoImplicit false

open Regex (NFA)
open Regex.Data (BitMatrix BoundedIterator)
open Regex.Strategy (refineUpdate refineUpdateOpt refineUpdates materializeUpdates)
open String (Pos)
namespace Regex.Backtracker

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx bufferSize : Nat}

def StackEntry.Refines (entryH : StackEntry HistoryStrategy nfa startIdx maxIdx) (entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx) : Prop :=
  refineUpdate entryH.update entryB.update ∧ entryH.state = entryB.state ∧ entryH.it = entryB.it

theorem StackEntry.Refines.simpL {update state it} {entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx} (ref : StackEntry.Refines ⟨update, state, it⟩ entryB) :
  entryB = ⟨entryB.update, state, it⟩ := by
  unfold StackEntry.Refines at ref
  simp_all

theorem StackEntry.Refines.mk {update} {state state' : Fin nfa.nodes.size} {it it' : BoundedIterator startIdx maxIdx} {entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx}
  (ref : StackEntry.Refines ⟨update, state, it⟩ entryB) :
  StackEntry.Refines ⟨update, state', it'⟩ ⟨entryB.update, state', it'⟩ := by
  simp [Refines] at ref
  simp [Refines, ref]

theorem StackEntry.Refines.empty {state : Fin nfa.nodes.size} {it : BoundedIterator startIdx maxIdx} : StackEntry.Refines ⟨HistoryStrategy.empty, state, it⟩ ⟨(BufferStrategy bufferSize).empty, state, it⟩ := by
  simp [Refines]

inductive RefineStack : List (StackEntry HistoryStrategy nfa startIdx maxIdx) → List (StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx) → Prop where
  | nil : RefineStack [] []
  | cons (entryH entryB stackH stackB) : entryH.Refines entryB → RefineStack stackH stackB → RefineStack (entryH :: stackH) (entryB :: stackB)

def Refines (resultH : Option (List (Nat × Pos)) × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (resultB : Option (Buffer bufferSize) × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  refineUpdateOpt resultH.1 resultB.1 ∧ resultH.2 = resultB.2

theorem captureNextAux.pushNext.refines {nfa wf startIdx maxIdx bufferSize stackH stackB updateH updateB state it}
  (refEntry : StackEntry.Refines ⟨updateH, state, it⟩ ⟨updateB, state, it⟩) (refStack : RefineStack stackH stackB) :
  RefineStack (captureNextAux.pushNext HistoryStrategy nfa wf startIdx maxIdx stackH updateH state it) (captureNextAux.pushNext (BufferStrategy bufferSize) nfa wf startIdx maxIdx stackB updateB state it) := by
  cases stackH, updateH, state, it using captureNextAux.pushNext.fun_cases' HistoryStrategy nfa wf startIdx maxIdx with
  | done stackH updateH state it hn => simp [pushNext.done hn, refStack]
  | fail stackH updateH state it hn => simp [pushNext.fail hn, refStack]
  | epsilon stackH updateH state it state' hn =>
    simp [pushNext.epsilon hn]
    exact .cons _ _ _ _ refEntry.mk refStack
  | split stackH updateH state it state₁ state₂ hn =>
    simp [pushNext.split hn]
    exact .cons _ _ _ _ refEntry.mk (.cons _ _ _ _ refEntry.mk refStack)
  | save stackH updateH state it offset state' hn =>
    -- This is the only interesting case, where we update the history/buffer
    simp [pushNext.save hn]
    refine .cons _ _ _ _ ?_ refStack
    simp [StackEntry.Refines, refineUpdate] at refEntry
    simp [StackEntry.Refines, refineUpdate, HistoryStrategy, BufferStrategy, refEntry]
  | anchor_pos stackH updateH state it a state' hn ht =>
    simp [pushNext.anchor_pos hn ht]
    exact .cons _ _ _ _ refEntry.mk refStack
  | anchor_neg stackH updateH state it a state' hn ht => simp [pushNext.anchor_neg hn ht, refStack]
  | char_pos stackH updateH state it c state' hn hnext hc =>
    simp [pushNext.char_pos hn hnext hc]
    exact .cons _ _ _ _ refEntry.mk refStack
  | char_neg stackH updateH state it c state' hn h => simp [pushNext.char_neg hn h, refStack]
  | sparse_pos stackH updateH state it cs state' hn hnext hc =>
    simp [pushNext.sparse_pos hn hnext hc]
    exact .cons _ _ _ _ refEntry.mk refStack
  | sparse_neg stackH updateH state it cs state' hn h => simp [pushNext.sparse_neg hn h, refStack]

theorem captureNextAux.refines (nfa wf startIdx maxIdx bufferSize visited) {stackH stackB} (refStack : RefineStack stackH stackB) :
  Refines (captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stackH) (captureNextAux (BufferStrategy bufferSize) nfa wf startIdx maxIdx visited stackB) := by
  induction visited, stackH using captureNextAux.induct' HistoryStrategy nfa wf startIdx maxIdx generalizing stackB with
  | base visited =>
    cases refStack with
    | nil => simp [captureNextAux_base, Refines, refineUpdateOpt]
  | visited visited update state' it stackH mem ih =>
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_visited mem]
      exact ih refStack
  | done visited update state' it stackH mem hn =>
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_done mem hn, Refines, refineUpdateOpt, refEntry.1]
  | next visited update state' it stackH mem hn ih =>
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_next mem hn]
      exact ih (pushNext.refines (refEntry.simpL ▸ refEntry) refStack)

theorem captureNext.go.refines (nfa wf startIdx bufferSize bit visited) :
  refineUpdateOpt (captureNext.go HistoryStrategy nfa wf startIdx maxIdx bit visited) (captureNext.go (BufferStrategy bufferSize) nfa wf startIdx maxIdx bit visited) := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | found bit visited updateH visitedH hauxH =>
    let entryH : StackEntry HistoryStrategy nfa startIdx maxIdx := ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩
    let entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx := ⟨(BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩, bit⟩
    have refStack : RefineStack [entryH] [entryB] := .cons entryH entryB [] [] .empty .nil
    have refResult := captureNextAux.refines nfa wf startIdx maxIdx bufferSize visited refStack
    match hauxB : captureNextAux (BufferStrategy bufferSize) nfa wf startIdx maxIdx visited [entryB] with
    | (.some updateB, visitedB) =>
      simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
      simp [captureNext.go_found hauxH, captureNext.go_found hauxB, Refines, refineUpdateOpt, refResult]
    | (.none, _) => simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
  | not_found_next bit visited visitedH hauxH hnext ih =>
    let entryH : StackEntry HistoryStrategy nfa startIdx maxIdx := ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩
    let entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx := ⟨(BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩, bit⟩
    have refStack : RefineStack [entryH] [entryB] := .cons entryH entryB [] [] .empty .nil
    have refResult := captureNextAux.refines nfa wf startIdx maxIdx bufferSize visited refStack
    match hauxB : captureNextAux (BufferStrategy bufferSize) nfa wf startIdx maxIdx visited [entryB] with
    | (.some _, _) => simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
    | (.none, visitedB) =>
      simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
      simp [captureNext.go_not_found_next hauxH hnext, captureNext.go_not_found_next hauxB hnext]
      exact refResult ▸ ih
  | not_found_end bit visited visitedH hauxH hnext =>
    let entryH : StackEntry HistoryStrategy nfa startIdx maxIdx := ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩
    let entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx := ⟨(BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩, bit⟩
    have refStack : RefineStack [entryH] [entryB] := .cons entryH entryB [] [] .empty .nil
    have refResult := captureNextAux.refines nfa wf startIdx maxIdx bufferSize visited refStack
    match hauxB : captureNextAux (BufferStrategy bufferSize) nfa wf startIdx maxIdx visited [entryB] with
    | (.some _, _) => simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
    | (.none, visitedB) =>
      simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
      simp [captureNext.go_not_found_end hauxH hnext, captureNext.go_not_found_end hauxB hnext, Refines, refineUpdateOpt, refResult]

theorem captureNext.refines (nfa wf bufferSize it) :
  refineUpdateOpt (captureNext HistoryStrategy nfa wf it) (captureNext (BufferStrategy bufferSize) nfa wf it) := by
  if le : it.pos ≤ it.toString.endPos then
    simp [captureNext_le le]
    exact (captureNext.go.refines nfa wf it.pos.byteIdx bufferSize ⟨it, Nat.le_refl _, le, rfl⟩ (BitMatrix.zero _ _))
  else
    simp [captureNext_not_le le, refineUpdateOpt]

end Regex.Backtracker
