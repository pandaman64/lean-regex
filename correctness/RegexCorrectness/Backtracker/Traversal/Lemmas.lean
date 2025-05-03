import RegexCorrectness.Backtracker.Traversal.Invariants

set_option autoImplicit false

open Regex.Data (BitMatrix BoundedIterator)
open String (Pos)

namespace Regex.Backtracker

namespace captureNextAux

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ bit : BoundedIterator startIdx maxIdx}
  {visited₀ visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}

theorem PathClosure.preserves {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (v : bit.Valid) (isNextN : bit.IsNextNOf bit₀) (cls : PathClosure bit₀ visited) :
  PathClosure bit₀ result.2 := by
  have cinv : ClosureInv bit₀ visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] := by
    intro state bit state' bit' update isNextN hmem step
    exact .inl (cls state bit state' bit' (List.ofOption update) isNextN hmem (.last step))
  exact path_closure hres isNone isNextN cinv (StackInv.intro v)

theorem mem_or_path_of_mem_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (v : bit.Valid) :
  VisitedInv wf bit visited result.2 :=
  visited_inv_of_none hres isNone VisitedInv.rfl (StackInv.intro v)

theorem mem_of_path_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (v : bit.Valid) (isNextN : bit.IsNextNOf bit₀) (cls : PathClosure bit₀ visited)
  (bit' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (update : List (Nat × Pos)) (path : Path nfa wf bit.it bit'.it state update) :
  result.2.get state bit'.index := by
  have mem_start : result.2.get ⟨nfa.start, wf.start_lt⟩ bit.index := hres ▸ mem_stack_top ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩ [] rfl
  match path.eq_or_nfaPath with
  | .inl ⟨eqit, eqstate, _⟩ =>
    have eq : bit' = bit := BoundedIterator.ext eqit
    simpa [eq, ←eqstate] using mem_start
  | .inr path =>
    have cls' : PathClosure bit₀ result.2 := cls.preserves hres isNone v isNextN
    exact cls' ⟨nfa.start, wf.start_lt⟩ bit state bit' update isNextN mem_start path

theorem mem_iff_mem_or_path_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (v : bit.Valid) (isNextN : bit.IsNextNOf bit₀) (cls : PathClosure bit₀ visited)
  (bit' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (isNextN' : bit'.IsNextNOf bit) :
  result.2.get state bit'.index ↔ visited.get state bit'.index ∨ ∃ update, Path nfa wf bit.it bit'.it state update := by
  apply Iff.intro
  . intro mem
    exact mem_or_path_of_mem_of_none hres isNone v state bit' isNextN' mem
  . intro h
    match h with
    | .inl mem => exact hres ▸ mem_of_mem_visited mem
    | .inr ⟨update, path⟩ => exact mem_of_path_of_none hres isNone v isNextN cls bit' state update path

end captureNextAux

namespace captureNext.go

open captureNextAux (StackInv VisitedInv NotDoneInv)

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ bit : BoundedIterator startIdx maxIdx} {visited₀ visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)}

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

end captureNext.go

end Regex.Backtracker
