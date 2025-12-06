import RegexCorrectness.Backtracker.Traversal.Invariants

set_option autoImplicit false

open Regex.Data (BitMatrix BVPos)
open String (ValidPos)

namespace Regex.Backtracker

namespace captureNextAux

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : ValidPos s} {bvpos₀ bvpos : BVPos startPos}
  {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {stack : List (StackEntry (HistoryStrategy s) nfa startPos)}

theorem mem_or_path_of_mem_of_none {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] = result)
  (isNone : result.1 = .none) :
  VisitedInv wf bvpos₀ bvpos visited result.2 :=
  visited_inv_of_none hres isNone (VisitedInv.rfl wf bvpos₀ bvpos) (StackInv.intro bvpos)

theorem PathClosure.preserves {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] = result)
  (isNone : result.1 = .none) (cls : PathClosure bvpos₀ visited) :
  PathClosure bvpos₀ result.2 := by
  have cinv : ClosureInv bvpos₀ visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] := by
    intro state bvpos state' bvpos' update le hmem step
    exact .inl (cls state bvpos state' bvpos' (List.ofOption update) le hmem (.last step))
  exact path_closure hres isNone cinv (StackInv.intro bvpos)

theorem mem_of_path_of_none {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] = result)
  (isNone : result.1 = .none) (le₀ : bvpos₀ ≤ bvpos) (cls : PathClosure bvpos₀ visited)
  (bvpos' : BVPos startPos) (state : Fin nfa.nodes.size) (update : List (Nat × ValidPos s)) (path : Path nfa wf bvpos.current bvpos'.current state update) :
  result.2.get state bvpos'.index := by
  have mem_start : result.2.get ⟨nfa.start, wf.start_lt⟩ bvpos.index := hres ▸ mem_stack_top ⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩ [] rfl
  match path.eq_or_nfaPath with
  | .inl ⟨eqpos, eqstate, _⟩ =>
    have eq : bvpos' = bvpos := BVPos.ext eqpos
    simpa [eq, ←eqstate] using mem_start
  | .inr path =>
    have cls' : PathClosure bvpos₀ result.2 := cls.preserves hres isNone
    exact cls' ⟨nfa.start, wf.start_lt⟩ bvpos state bvpos' update le₀ mem_start path

theorem mem_iff_mem_or_path_of_none {result} (hres : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] = result)
  (isNone : result.1 = .none) (le₀ : bvpos₀ ≤ bvpos) (cls : PathClosure bvpos₀ visited)
  (bvpos' : BVPos startPos) (state : Fin nfa.nodes.size) (le₀' : bvpos₀ ≤ bvpos') :
  result.2.get state bvpos'.index ↔ visited.get state bvpos'.index ∨ ∃ update, Path nfa wf bvpos.current bvpos'.current state update := by
  apply Iff.intro
  . intro mem
    exact mem_or_path_of_mem_of_none hres isNone state bvpos' le₀' mem
  . intro h
    match h with
    | .inl mem => exact hres ▸ mem_of_mem_visited mem
    | .inr ⟨update, path⟩ => exact mem_of_path_of_none hres isNone le₀ cls bvpos' state update path

end captureNextAux

namespace captureNext.go

open captureNextAux (StackInv NotDoneInv PathClosure)

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {startPos : ValidPos s} {bvpos₀ bvpos : BVPos startPos} {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {stack : List (StackEntry (HistoryStrategy s) nfa startPos)}

structure Inv (wf : nfa.WellFormed) (bvpos₀ bvpos : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) : Prop where
  closure : PathClosure bvpos₀ visited
  mem_iff_path : ∀ (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos),
    bvpos₀ ≤ bvpos' →
    (visited.get state' bvpos'.index ↔
      ∃ (bvposPrev : BVPos startPos) (update : List (Nat × ValidPos s)),
        bvpos₀ ≤ bvposPrev ∧ bvposPrev < bvpos ∧ Path nfa wf bvposPrev.current bvpos'.current state' update)

namespace Inv

theorem zero : Inv wf bvpos₀ bvpos₀ (BitMatrix.zero nfa.nodes.size (startPos.remainingBytes + 1)) := by
  refine ⟨PathClosure.zero, ?_⟩
  simp only [BitMatrix.get_zero, Bool.false_eq_true, exists_and_left, false_iff, not_exists, not_and]
  intro _ _ _ bvpos le lt
  exact (BVPos.not_lt_of_le le lt).elim

theorem mem_iff_of_aux_none {result} (haux : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] = result)
  (isNone : result.1 = .none) (le₀ : bvpos₀ ≤ bvpos) (inv : Inv wf bvpos₀ bvpos visited)
  (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos) (le₀' : bvpos₀ ≤ bvpos') :
  result.2.get state' bvpos'.index ↔
    (∃ (bvposPrev : BVPos startPos) (update : List (Nat × ValidPos s)), bvpos₀ ≤ bvposPrev ∧ bvposPrev < bvpos ∧ Path nfa wf bvposPrev.current bvpos'.current state' update) ∨
      ∃ (update : List (Nat × ValidPos s)), Path nfa wf bvpos.current bvpos'.current state' update := by
  rw [captureNextAux.mem_iff_mem_or_path_of_none haux isNone le₀ inv.closure bvpos' state' le₀']
  rw [inv.mem_iff_path state' bvpos' le₀']

theorem preservesAux {result} (haux : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, bvpos⟩] = result)
  (isNone : result.1 = .none) (ne : bvpos ≠ s.endBVPos startPos) (le₀ : bvpos₀ ≤ bvpos)
  (inv : Inv wf bvpos₀ bvpos visited) :
  Inv wf bvpos₀ (bvpos.next ne) result.2 := by
  refine ⟨inv.closure.preserves haux isNone, ?_⟩
  intro state' bvpos' le₀'
  rw [inv.mem_iff_of_aux_none haux isNone le₀ state' bvpos' le₀']
  have {bvposPrev} : bvposPrev < bvpos.next ne ↔ bvposPrev < bvpos ∨ bvposPrev = bvpos := by
    sorry
  grind

theorem mem_iff_path_of_aux_none_endBVPos {result}
  (haux : captureNextAux (HistoryStrategy s) nfa wf startPos visited [⟨(HistoryStrategy s).empty, ⟨nfa.start, wf.start_lt⟩, s.endBVPos startPos⟩] = result)
  (isNone : result.1 = .none) (inv : Inv wf bvpos₀ (s.endBVPos startPos) visited)
  (state' : Fin nfa.nodes.size) (bvpos' : BVPos startPos) (le₀' : bvpos₀ ≤ bvpos') :
  result.2.get state' bvpos'.index ↔
    ∃ (bvposPrev : BVPos startPos) (update : List (Nat × ValidPos s)), bvpos₀ ≤ bvposPrev ∧ Path nfa wf bvposPrev.current bvpos'.current state' update := by
  rw [inv.mem_iff_of_aux_none haux isNone bvpos₀.le_endBVPos state' bvpos' le₀']
  apply Iff.intro
  . intro h
    match h with
    | .inl ⟨bvposPrev, update, le, lt, path⟩ => exact ⟨bvposPrev, update, le, path⟩
    | .inr ⟨update, path⟩ => exact ⟨s.endBVPos startPos, update, bvpos₀.le_endBVPos, path⟩
  . intro ⟨bvpos, update, le, path⟩
    cases BVPos.lt_or_eq_of_le bvpos.le_endBVPos with
    | inl lt => exact .inl ⟨bvpos, update, le, lt, path⟩
    | inr eq => exact .inr ⟨update, eq ▸ path⟩

end Inv

theorem ne_done_of_path_of_none (hres : go (HistoryStrategy s) nfa wf startPos bvpos visited = .none)
  (le₀ : bvpos₀ ≤ bvpos)
  (inv : Inv wf bvpos₀ bvpos visited) (ndinv : NotDoneInv visited) :
  ∀ (bvpos' bvpos'' : BVPos startPos) (state : Fin nfa.nodes.size) (update : List (Nat × ValidPos s)),
    bvpos₀ ≤ bvpos' →
    Path nfa wf bvpos'.current bvpos''.current state update →
    nfa[state] ≠ .done := by
  induction bvpos, visited using captureNext.go.induct' (HistoryStrategy s) nfa wf startPos with
  | found bvpos visited update visited' haux =>
    simp [captureNext.go_found haux] at hres
  | not_found_next bvpos visited visited' haux ne ih =>
    rw [captureNext.go_not_found_next haux ne] at hres
    have inv' : Inv wf bvpos₀ (bvpos.next ne) visited' := inv.preservesAux haux rfl ne le₀
    have ndinv' : NotDoneInv visited' := captureNextAux.not_done_of_none haux rfl ndinv
    exact ih hres (BVPos.le_trans le₀ (BVPos.le_of_lt (BVPos.lt_next ne))) inv' ndinv'
  | not_found_end bvpos visited visited' haux eq =>
    rw [captureNext.go_not_found_end haux eq] at hres
    simp only [ne_eq, Decidable.not_not] at eq
    subst bvpos

    intro bvpos' bvpos'' state update le₀' path hn
    have le₀'' : bvpos₀ ≤ bvpos'' := BVPos.le_trans le₀' path.le
    have mem : visited'.get state bvpos''.index :=
      (inv.mem_iff_path_of_aux_none_endBVPos haux rfl state bvpos'' le₀'').mpr ⟨bvpos', update, le₀', path⟩

    have ndinv' : NotDoneInv visited' := captureNextAux.not_done_of_none haux rfl ndinv
    exact ndinv' state bvpos'' mem hn

theorem path_done_of_some {update} (hres : go (HistoryStrategy s) nfa wf startPos bvpos visited = .some update) :
  ∃ (state : Fin nfa.nodes.size) (bvpos' bvpos'' : BVPos startPos),
    nfa[state] = .done ∧ bvpos ≤ bvpos' ∧ Path nfa wf bvpos'.current bvpos''.current state update := by
  induction bvpos, visited using go.induct' (HistoryStrategy s) nfa wf startPos with
  | found bvpos visited update visited' haux =>
    simp [captureNext.go_found haux] at hres
    simp [hres] at haux
    have inv₀ : StackInv wf bvpos [⟨[], ⟨nfa.start, wf.start_lt⟩, bvpos⟩] := by
      simpa [StackInv] using .init
    have ⟨state, bvpos', hn, le, path⟩ := captureNextAux.path_done_of_some haux inv₀
    exact ⟨state, bvpos, bvpos', hn, BVPos.le_refl _, path⟩
  | not_found_next bvpos visited visited' haux ne ih =>
    simp [captureNext.go_not_found_next haux ne] at hres
    have ⟨state, bvpos', bvpos'', hn, le, path⟩ := ih hres
    exact ⟨state, bvpos', bvpos'', hn, BVPos.le_trans (BVPos.le_of_lt (BVPos.lt_next ne)) le, path⟩
  | not_found_end bvpos visited visited' haux ne => simp [captureNext.go_not_found_end haux ne] at hres

end captureNext.go

end Regex.Backtracker
