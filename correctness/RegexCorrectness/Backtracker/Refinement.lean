import RegexCorrectness.Backtracker.Traversal
import RegexCorrectness.Strategy

set_option autoImplicit false

open Regex (NFA)
open Regex.Data (BoundedIterator)
open Regex.Strategy (refineUpdate refineUpdateOpt refineUpdates materializeUpdates)
open String (Pos)
namespace Regex.Backtracker

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx bufferSize : Nat}

def StackEntry.Refines (entryH : StackEntry HistoryStrategy nfa startIdx maxIdx) (entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx) : Prop :=
  refineUpdate entryH.update entryB.update ∧ entryH.state = entryB.state ∧ entryH.it = entryB.it

theorem StackEntry.Refines.simpL {update state it eq} {entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx} (ref : StackEntry.Refines ⟨update, state, it, eq⟩ entryB) :
  entryB = ⟨entryB.update, state, it, eq⟩ := by
  unfold StackEntry.Refines at ref
  simp_all

theorem StackEntry.Refines.mk {update} {state state' : Fin nfa.nodes.size} {it it' : BoundedIterator startIdx} {eq : it.maxIdx = maxIdx} {eq' : it'.maxIdx = maxIdx} {entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx}
  (ref : StackEntry.Refines ⟨update, state, it, eq⟩ entryB) :
  StackEntry.Refines ⟨update, state', it', eq'⟩ ⟨entryB.update, state', it', eq'⟩ := by
  simp [Refines] at ref
  simp [Refines, ref]

theorem StackEntry.Refines.empty {state : Fin nfa.nodes.size} {it : BoundedIterator startIdx} {eq : it.maxIdx = maxIdx} : StackEntry.Refines ⟨HistoryStrategy.empty, state, it, eq⟩ ⟨(BufferStrategy bufferSize).empty, state, it, eq⟩ := by
  simp [Refines]

inductive RefineStack : List (StackEntry HistoryStrategy nfa startIdx maxIdx) → List (StackEntry (BufferStrategy bufferSize) nfa startIdx maxIdx) → Prop where
  | nil : RefineStack [] []
  | cons (entryH entryB stackH stackB) : entryH.Refines entryB → RefineStack stackH stackB → RefineStack (entryH :: stackH) (entryB :: stackB)

def Refines (resultH : Option (List (Nat × Pos)) × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (resultB : Option (Buffer bufferSize) × BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  refineUpdateOpt resultH.1 resultB.1 ∧ resultH.2 = resultB.2

theorem captureNextAux.refines (nfa wf startIdx maxIdx bufferSize visited) {stackH stackB} (refStack : RefineStack stackH stackB) :
  Refines (captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited stackH) (captureNextAux (BufferStrategy bufferSize) nfa wf startIdx maxIdx visited stackB) := by
  induction visited, stackH using captureNextAux.induct' HistoryStrategy nfa wf startIdx maxIdx generalizing stackB with
  | base visited =>
    cases refStack with
    | nil => simp [captureNextAux_base, Refines, refineUpdateOpt]
  | visited visited update state' it eq stackH mem ih =>
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_visited mem]
      exact ih refStack
  | done visited update state' it eq stackH mem hn =>
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_done mem hn, Refines, refineUpdateOpt, refEntry.1]
  | fail visited update state' it eq stackH mem hn =>
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_fail mem hn, Refines, refineUpdateOpt]
  | epsilon visited update state it eq stackH mem visited' state' hn =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_epsilon mem hn]
      exact ih (.cons _ _ _ _ refEntry.mk refStack)
  | split visited update state it eq stackH mem visited' state₁ state₂ hn =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_split mem hn]
      exact ih (.cons _ _ _ _ refEntry.mk (.cons _ _ _ _ refEntry.mk refStack))
  | save visited update state it eq stackH mem visited' offset state' hn update' =>
    -- This is the only interesting case, where we update the history/buffer
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_save mem hn]
      refine ih (.cons _ _ _ _ ?_ refStack)
      simp [StackEntry.Refines, refineUpdate] at refEntry
      simp [StackEntry.Refines, update', refineUpdate, HistoryStrategy, BufferStrategy, refEntry.1]
  | anchor_pos visited update state it eq stackH mem visited' a state' hn ht =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_anchor_pos mem hn ht]
      exact ih (.cons _ _ _ _ refEntry.mk refStack)
  | anchor_neg visited update state it eq stackH mem visited' a state' hn ht =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_anchor_neg mem hn ht]
      exact ih refStack
  | char_pos visited update state it eq stackH mem visited' c state' hn hnext hc =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_char_pos mem hn hnext hc]
      exact ih (.cons _ _ _ _ refEntry.mk refStack)
  | char_neg visited update state it eq stackH mem visited' c state' hn hnext hc =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_char_neg mem hn hnext hc]
      exact ih refStack
  | char_end visited update state it eq stackH mem visited' c state' hn hnext =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_char_end mem hn hnext]
      exact ih refStack
  | sparse_pos visited update state it eq stackH mem visited' cs state' hn hnext hc =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_sparse_pos mem hn hnext hc]
      exact ih (.cons _ _ _ _ refEntry.mk refStack)
  | sparse_neg visited update state it eq stackH mem visited' cs state' hn hnext hc =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_sparse_neg mem hn hnext hc]
      exact ih refStack
  | sparse_end visited update state it eq stackH mem visited' cs state' hn hnext =>
    rename_i ih
    cases refStack with
    | cons entryH entryB stackH stackB refEntry refStack =>
      rw [refEntry.simpL]
      simp [captureNextAux_sparse_end mem hn hnext]
      exact ih refStack

theorem captureNext.go.refines (nfa wf startIdx bufferSize bit visited) :
  Refines (captureNext.go HistoryStrategy nfa wf startIdx bit visited) (captureNext.go (BufferStrategy bufferSize) nfa wf startIdx bit visited) := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx with
  | found bit visited updateH visitedH hauxH =>
    let entryH : StackEntry HistoryStrategy nfa startIdx bit.maxIdx := ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩
    let entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx bit.maxIdx := ⟨(BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩
    have refStack : RefineStack [entryH] [entryB] := .cons entryH entryB [] [] .empty .nil
    have refResult := captureNextAux.refines nfa wf startIdx bit.maxIdx bufferSize visited refStack
    match hauxB : captureNextAux (BufferStrategy bufferSize) nfa wf startIdx bit.maxIdx visited [entryB] with
    | (.some updateB, visitedB) =>
      simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
      simp [captureNext.go_found hauxH, captureNext.go_found hauxB, Refines, refineUpdateOpt, refResult]
    | (.none, _) => simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
  | not_found_next bit visited visitedH hauxH hnext ih =>
    let entryH : StackEntry HistoryStrategy nfa startIdx bit.maxIdx := ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩
    let entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx bit.maxIdx := ⟨(BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩
    have refStack : RefineStack [entryH] [entryB] := .cons entryH entryB [] [] .empty .nil
    have refResult := captureNextAux.refines nfa wf startIdx bit.maxIdx bufferSize visited refStack
    match hauxB : captureNextAux (BufferStrategy bufferSize) nfa wf startIdx bit.maxIdx visited [entryB] with
    | (.some _, _) => simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
    | (.none, visitedB) =>
      simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
      simp [captureNext.go_not_found_next hauxH hnext, captureNext.go_not_found_next hauxB hnext]
      exact refResult ▸ ih
  | not_found_end bit visited visitedH hauxH hnext =>
    let entryH : StackEntry HistoryStrategy nfa startIdx bit.maxIdx := ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩
    let entryB : StackEntry (BufferStrategy bufferSize) nfa startIdx bit.maxIdx := ⟨(BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩
    have refStack : RefineStack [entryH] [entryB] := .cons entryH entryB [] [] .empty .nil
    have refResult := captureNextAux.refines nfa wf startIdx bit.maxIdx bufferSize visited refStack
    match hauxB : captureNextAux (BufferStrategy bufferSize) nfa wf startIdx bit.maxIdx visited [entryB] with
    | (.some _, _) => simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
    | (.none, visitedB) =>
      simp [Refines, entryH, hauxH, hauxB, refineUpdateOpt] at refResult
      simp [captureNext.go_not_found_end hauxH hnext, captureNext.go_not_found_end hauxB hnext, Refines, refineUpdateOpt, refResult]

theorem captureNext.refines (nfa wf bufferSize it) :
  refineUpdateOpt (captureNext HistoryStrategy nfa wf it) (captureNext (BufferStrategy bufferSize) nfa wf it) := by
  if le : it.pos ≤ it.toString.endPos then
    simp [captureNext_le le]
    exact (captureNext.go.refines nfa wf it.pos.byteIdx bufferSize ⟨it, Nat.le_refl _, le⟩ (BitMatrix.zero _ _)).1
  else
    simp [captureNext_not_le le, refineUpdateOpt]

end Regex.Backtracker
