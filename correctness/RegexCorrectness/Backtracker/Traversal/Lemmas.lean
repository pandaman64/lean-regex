import RegexCorrectness.Backtracker.Traversal.Invariants

set_option autoImplicit false

open Regex.Data (BitMatrix BoundedIterator)
open String (Pos)

namespace Regex.Backtracker

namespace captureNextAux

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ bit : BoundedIterator startIdx maxIdx}
  {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)} {stack : List (StackEntry HistoryStrategy nfa startIdx maxIdx)}

theorem mem_or_path_of_mem_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches : bit₀.Reaches bit) :
  VisitedInv wf bit₀ bit reaches visited result.2 :=
  visited_inv_of_none hres isNone (VisitedInv.rfl reaches) (StackInv.intro reaches.validR)

theorem PathClosure.preserves {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches : bit₀.Reaches bit) (cls : PathClosure bit₀ visited) :
  PathClosure bit₀ result.2 := by
  have cinv : ClosureInv bit₀ visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] := by
    intro state bit state' bit' update reaches hmem step
    exact .inl (cls state bit state' bit' (List.ofOption update) reaches hmem (.last step))
  exact path_closure hres isNone reaches cinv (StackInv.intro reaches.validR)

theorem mem_of_path_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches : bit₀.Reaches bit) (cls : PathClosure bit₀ visited)
  (bit' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (update : List (Nat × Pos.Raw)) (path : Path nfa wf bit.it bit'.it state update) :
  result.2.get state bit'.index := by
  have mem_start : result.2.get ⟨nfa.start, wf.start_lt⟩ bit.index := hres ▸ mem_stack_top ⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩ [] rfl
  match path.eq_or_nfaPath with
  | .inl ⟨eqit, eqstate, _⟩ =>
    have eq : bit' = bit := BoundedIterator.ext eqit
    simpa [eq, ←eqstate] using mem_start
  | .inr path =>
    have cls' : PathClosure bit₀ result.2 := cls.preserves hres isNone reaches
    exact cls' ⟨nfa.start, wf.start_lt⟩ bit state bit' update reaches mem_start path

theorem mem_iff_mem_or_path_of_none {result} (hres : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches : bit₀.Reaches bit) (cls : PathClosure bit₀ visited)
  (bit' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (reaches' : bit₀.Reaches bit') :
  result.2.get state bit'.index ↔ visited.get state bit'.index ∨ ∃ update, Path nfa wf bit.it bit'.it state update := by
  apply Iff.intro
  . intro mem
    exact mem_or_path_of_mem_of_none hres isNone reaches state bit' reaches' mem
  . intro h
    match h with
    | .inl mem => exact hres ▸ mem_of_mem_visited mem
    | .inr ⟨update, path⟩ => exact mem_of_path_of_none hres isNone reaches cls bit' state update path

end captureNextAux

namespace captureNext.go

open captureNextAux (StackInv NotDoneInv PathClosure)

variable {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit₀ bit : BoundedIterator startIdx maxIdx} {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)}

structure Inv (wf : nfa.WellFormed) (bit₀ bit : BoundedIterator startIdx maxIdx) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) : Prop where
  closure : PathClosure bit₀ visited
  mem_iff_path : ∀ (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx),
    bit₀.Reaches bit' →
    (visited.get state' bit'.index ↔ ∃ (bitPrev : BoundedIterator startIdx maxIdx) (update : List (Nat × Pos.Raw)), bitPrev.BetweenE bit₀ bit ∧ Path nfa wf bitPrev.it bit'.it state' update)

namespace Inv

theorem zero : Inv wf bit₀ bit₀ (BitMatrix.zero nfa.nodes.size (maxIdx + 1 - startIdx)) := ⟨PathClosure.zero, by simp⟩

theorem mem_iff_of_aux_none {result} (haux : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches : bit₀.Reaches bit) (inv : Inv wf bit₀ bit visited)
  (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx) (reaches' : bit₀.Reaches bit') :
  result.2.get state' bit'.index ↔
    (∃ (bitPrev : BoundedIterator startIdx maxIdx) (update : List (Nat × Pos.Raw)), bitPrev.BetweenE bit₀ bit ∧ Path nfa wf bitPrev.it bit'.it state' update) ∨
      ∃ (update : List (Nat × Pos.Raw)), Path nfa wf bit.it bit'.it state' update := by
  rw [captureNextAux.mem_iff_mem_or_path_of_none haux isNone reaches inv.closure bit' state' reaches']
  rw [inv.mem_iff_path state' bit' reaches']

theorem preservesAux {result} (haux : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (hnext : bit.hasNext) (reaches : bit₀.Reaches bit)
  (inv : Inv wf bit₀ bit visited) :
  Inv wf bit₀ (bit.next hnext) result.2 := by
  refine ⟨inv.closure.preserves haux isNone reaches, ?_⟩
  intro state' bit' reaches'
  rw [inv.mem_iff_of_aux_none haux isNone reaches state' bit' reaches']
  simp only [exists_and_left, BoundedIterator.BetweenE.next_iff reaches.validR hnext, or_and_right,
    exists_or, existsAndEq, reaches, and_self, true_and]

theorem mem_iff_path_of_aux_none_of_not_hasNext {result} (haux : captureNextAux HistoryStrategy nfa wf startIdx maxIdx visited [⟨HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = result)
  (isNone : result.1 = .none) (reaches : bit₀.Reaches bit) (hnext : ¬bit.hasNext) (inv : Inv wf bit₀ bit visited)
  (state' : Fin nfa.nodes.size) (bit' : BoundedIterator startIdx maxIdx) (reaches' : bit₀.Reaches bit') :
  result.2.get state' bit'.index ↔ ∃ (bit : BoundedIterator startIdx maxIdx) (update : List (Nat × Pos.Raw)), bit₀.Reaches bit ∧ Path nfa wf bit.it bit'.it state' update := by
  rw [inv.mem_iff_of_aux_none haux isNone reaches state' bit' reaches']
  apply Iff.intro
  . intro h
    match h with
    | .inl ⟨bitPrev, update, between, path⟩ => exact ⟨bitPrev, update, between.2.1, path⟩
    | .inr ⟨update, path⟩ => exact ⟨bit, update, reaches, path⟩
  . have eq : bit = bit₀.toEnd := by
      simp [BoundedIterator.ext_pos_iff, reaches.toString.symm, bit₀.toEnd_pos, bit.pos_eq_of_not_hasNext hnext]
    subst bit
    intro ⟨bit, update, reaches, path⟩
    have between : bit.BetweenI bit₀ bit₀.toEnd := ⟨reaches, reaches.reaches_toEnd_of_reaches⟩
    simp [BoundedIterator.BetweenI.iffE] at between
    match between with
    | .inl between => exact .inl ⟨bit, update, between, path⟩
    | .inr ⟨_, eq⟩ => exact .inr ⟨update, eq ▸ path⟩

end Inv

theorem ne_done_of_path_of_none (hres : go HistoryStrategy nfa wf startIdx maxIdx bit visited = .none)
  (reaches : bit₀.Reaches bit)
  (inv : Inv wf bit₀ bit visited) (ndinv : NotDoneInv visited) :
  ∀ (bit' bit'' : BoundedIterator startIdx maxIdx) (state : Fin nfa.nodes.size) (update : List (Nat × Pos.Raw)),
    bit₀.Reaches bit' →
    Path nfa wf bit'.it bit''.it state update →
    nfa[state] ≠ .done := by
  induction bit, visited using captureNext.go.induct' HistoryStrategy nfa wf startIdx maxIdx with
  | found bit visited update visited' haux =>
    simp [captureNext.go_found haux] at hres
  | not_found_next bit visited visited' haux hnext ih =>
    rw [captureNext.go_not_found_next haux hnext] at hres
    have inv' : Inv wf bit₀ (bit.next hnext) visited' := inv.preservesAux haux rfl hnext reaches
    have ndinv' : NotDoneInv visited' := captureNextAux.not_done_of_none haux rfl ndinv
    exact ih hres (reaches.next' hnext) inv' ndinv'
  | not_found_end bit visited visited' haux hnext =>
    rw [captureNext.go_not_found_end haux hnext] at hres

    intro bit' bit'' state update reaches' path hn
    have reaches'' : bit₀.Reaches bit'' := reaches'.trans (path.reaches rfl)
    have mem : visited'.get state bit''.index := (inv.mem_iff_path_of_aux_none_of_not_hasNext haux rfl reaches hnext state bit'' reaches'').mpr ⟨bit', update, reaches', path⟩

    have ndinv' : NotDoneInv visited' := captureNextAux.not_done_of_none haux rfl ndinv
    exact ndinv' state bit'' mem hn

theorem path_done_of_some {nfa wf startIdx maxIdx bit update} {visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)}
  (v : bit.Valid) (hres : go HistoryStrategy nfa wf startIdx maxIdx bit visited = .some update) :
  ∃ (state : Fin nfa.nodes.size) (bit' bit'' : BoundedIterator startIdx maxIdx),
    nfa[state] = .done ∧ bit.Reaches bit' ∧ Path nfa wf bit'.it bit''.it state update := by
  induction bit, visited using go.induct' HistoryStrategy nfa wf startIdx with
  | found bit visited update' visited' haux =>
    simp [captureNext.go_found haux] at hres
    simp [hres] at haux
    have ⟨l, r, vf⟩ := v.validFor
    have inv₀ : StackInv wf bit [⟨[], ⟨nfa.start, wf.start_lt⟩, bit⟩] := by
      simp [StackInv]
      exact .init v
    have ⟨state, bit', hn, reaches, path⟩ := captureNextAux.path_done_of_some haux inv₀
    exact ⟨state, bit, bit', hn, .refl v, path⟩
  | not_found_next bit visited visited' haux hnext ih =>
    simp [captureNext.go_not_found_next haux hnext] at hres
    have ⟨state, bit', bit'', hn, reaches, path⟩ := ih (bit.next_valid hnext v) hres
    exact ⟨state, bit', bit'', hn, reaches.next v hnext, path⟩
  | not_found_end bit visited visited' haux hnext => simp [captureNext.go_not_found_end haux hnext] at hres

end captureNext.go

end Regex.Backtracker
