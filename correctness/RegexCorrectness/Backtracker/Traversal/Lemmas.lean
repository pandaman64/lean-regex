import RegexCorrectness.Backtracker.Traversal.Invariants

set_option autoImplicit false

open Regex.Data (BitMatrix BoundedIterator)
open String (Pos)

namespace Regex.Backtracker

namespace captureNextAux

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ bit : BoundedIterator startIdx maxIdx}
  {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}

theorem mem_or_path_of_mem_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (v : bit.Valid) :
  VisitedInv wf bit visited result.2 :=
  visited_inv_of_none hres isNone VisitedInv.rfl (StackInv.intro v)

theorem PathClosure.preserves {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches₀ : bit₀.Reaches bit) (cls : PathClosure bit₀ visited) :
  PathClosure bit₀ result.2 := by
  have cinv : ClosureInv bit₀ visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] := by
    intro state bit state' bit' update reaches hmem step
    exact .inl (cls state bit state' bit' (List.ofOption update) reaches hmem (.last step))
  exact path_closure hres isNone reaches₀ cinv (StackInv.intro reaches₀.validR)

theorem mem_of_path_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches₀ : bit₀.Reaches bit) (cls : PathClosure bit₀ visited)
  (bit' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (update : List (Nat × Pos)) (path : Path nfa wf bit.it bit'.it state update) :
  result.2.get state bit'.index := by
  have mem_start : result.2.get ⟨nfa.start, wf.start_lt⟩ bit.index := hres ▸ mem_stack_top ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩ [] rfl
  match path.eq_or_nfaPath with
  | .inl ⟨eqit, eqstate, _⟩ =>
    have eq : bit' = bit := BoundedIterator.ext eqit
    simpa [eq, ←eqstate] using mem_start
  | .inr path =>
    have cls' : PathClosure bit₀ result.2 := cls.preserves hres isNone reaches₀
    exact cls' ⟨nfa.start, wf.start_lt⟩ bit state bit' update reaches₀ mem_start path

theorem mem_iff_mem_or_path_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches₀ : bit₀.Reaches bit) (cls : PathClosure bit₀ visited)
  (bit' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (reaches : bit.Reaches bit') :
  result.2.get state bit'.index ↔ visited.get state bit'.index ∨ ∃ update, Path nfa wf bit.it bit'.it state update := by
  apply Iff.intro
  . intro mem
    exact mem_or_path_of_mem_of_none hres isNone reaches₀.validR state bit' reaches mem
  . intro h
    match h with
    | .inl mem => exact hres ▸ mem_of_mem_visited mem
    | .inr ⟨update, path⟩ => exact mem_of_path_of_none hres isNone reaches₀ cls bit' state update path

end captureNextAux

namespace captureNext.go

open captureNextAux (StackInv NotDoneInv PathClosure)

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ bit : BoundedIterator startIdx maxIdx} {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)}

theorem not_done_of_none {result} (hres : go HistoryStrategy nfa wf startIdx maxIdx bit visited = result)
  (isNone : result.1 = .none)
  (ndinv : NotDoneInv visited) :
  NotDoneInv result.2 := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | found bit visited update visited' haux =>
    rw [captureNext.go_found haux] at hres
    simp [←hres] at isNone
  | not_found_next bit visited visited' haux hnext ih =>
    rw [captureNext.go_not_found_next haux hnext] at hres
    have ndinv' : NotDoneInv visited' := captureNextAux.not_done_of_none haux rfl ndinv
    exact ih hres ndinv'
  | not_found_end bit visited visited' haux hnext =>
    rw [captureNext.go_not_found_end haux hnext] at hres
    have ndinv' : NotDoneInv visited' := captureNextAux.not_done_of_none haux rfl ndinv
    simpa [←hres] using ndinv'

structure Inv (wf : nfa.WellFormed) (bit₀ bit : BoundedIterator startIdx maxIdx) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop where
  closure : PathClosure bit₀ visited
  mem_iff_path : ∀ (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx),
    bit₀.Reaches bit' →
    (visited.get state' bit'.index ↔ ∃ (bitPrev : BoundedIterator startIdx maxIdx) (update : List (Nat × Pos)), bitPrev.BetweenE bit₀ bit ∧ Path nfa wf bitPrev.it bit'.it state' update)

namespace Inv

theorem preservesAux {result} (haux : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (hnext : bit.hasNext) (reaches : bit₀.Reaches bit)
  (inv : Inv wf bit₀ bit visited) :
  Inv wf bit₀ (bit.next hnext) result.2 := by
  refine ⟨inv.closure.preserves haux isNone reaches, ?_⟩
  intro state' bit' reaches'
  rw [captureNextAux.mem_iff_mem_or_path_of_none haux isNone reaches inv.closure bit' state' sorry]
  rw [inv.mem_iff_path state' bit' reaches']
  simp only [exists_and_left, BoundedIterator.BetweenE.next_iff reaches.validR hnext, or_and_right,
    exists_or, existsAndEq, reaches, and_self, true_and]

end Inv

def MemIffPathI (wf : nfa.WellFormed) (bit₀ : BoundedIterator startIdx maxIdx) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop :=
  ∀ (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx),
    bit₀.Reaches bit' →
    (visited.get state' bit'.index ↔ ∃ (bitPrev : BoundedIterator startIdx maxIdx) (update : List (Nat × Pos)), bitPrev.BetweenE bit₀ bit' ∧ Path nfa wf bitPrev.it bit'.it state' update)

theorem mem_iff_path_of_none {result} (hres : go HistoryStrategy nfa wf startIdx maxIdx bit visited = result)
  (isNone : result.1 = .none) (inv : Inv wf bit₀ bit visited) :
  MemIffPathI wf bit₀ result.2 := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | found bit visited update visited' haux =>
    rw [captureNext.go_found haux] at hres
    simp [←hres] at isNone
  | not_found_next bit visited visited' haux hnext ih =>
    rw [captureNext.go_not_found_next haux hnext] at hres
    exact ih hres (inv.preservesAux haux rfl hnext sorry)
  | not_found_end bit visited visited' haux hnext =>
    rw [captureNext.go_not_found_end haux hnext] at hres
    have eq : bit = bit₀.last := sorry
    subst bit

    intro state' bit' reaches'
    have := captureNextAux.mem_iff_mem_or_path_of_none haux rfl sorry inv.closure bit' state' -- ???
    sorry

end captureNext.go

end Regex.Backtracker
