module

public import Regex.Backtracker.Basic
import all Regex.Backtracker.Basic
public import RegexCorrectness.Backtracker.Model.Basic
import all RegexCorrectness.Backtracker.Model.Basic
import all RegexCorrectness.Backtracker.Basic
import RegexCorrectness.Data.BVPos
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

open String (Pos)
open Regex (NFA)
open Regex.Data (BitMatrix BVPos Anchor)
open Regex.Backtracker (StackEntry)
open Regex.Backtracker.captureNextAux (pushNext)

namespace Regex.Backtracker.Model

noncomputable def mapMatrix {s : String} {nfa : NFA} {startPos : Pos s} (matrix : BitMatrix nfa.size (startPos.remainingBytes + 1)) :
  Finset (Fin nfa.size × Pos s) :=
  { p : Fin nfa.size × Pos s | ∃ le : startPos ≤ p.2, matrix.get p.1 (BVPos.index ⟨p.2, le⟩) }

@[grind =, simp]
theorem mem_mapMatrix_iff {s : String} {nfa : NFA} {startPos : Pos s}
  (i : Fin nfa.size) (p : Pos s) (matrix : BitMatrix nfa.size (startPos.remainingBytes + 1)) :
  (i, p) ∈ mapMatrix matrix ↔ ∃ le : startPos ≤ p, matrix.get i (BVPos.index ⟨p, le⟩) := by
  grind [mapMatrix]

@[grind =, simp]
theorem mapMatrix_set {s : String} {nfa : NFA} {startPos : Pos s}
  (i : Fin nfa.size) (bp : BVPos startPos) (matrix : BitMatrix nfa.size (startPos.remainingBytes + 1)) :
  mapMatrix (matrix.set i bp.index) = insert ⟨i, bp.current⟩ (mapMatrix matrix) := by
  ext ⟨j, pj⟩
  rw [mem_mapMatrix_iff j pj _]
  apply Iff.intro
  . intro ⟨le, mem⟩
    simp only [BitMatrix.get_set, Bool.decide_or, Bool.decide_and, Bool.decide_eq_true,
      Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at mem
    match mem with
    | .inl ⟨eq₁, eq₂⟩ => simp [eq₁, BVPos.ext_index eq₂]
    | .inr mem => simp [le, mem]
  . intro mem
    simp only [Finset.mem_insert, Prod.mk.injEq, mem_mapMatrix_iff] at mem
    match mem with
    | .inl ⟨eq₁, eq₂⟩ =>
      have le : startPos ≤ pj := eq₂ ▸ bp.le
      have eq₂' : bp = ⟨pj, le⟩ := by simp [eq₂]
      exact ⟨le, by simp [BitMatrix.get_set, eq₁, eq₂']⟩
    | .inr ⟨le, mem⟩ => exact ⟨le, by simp [BitMatrix.get_set, mem]⟩

@[grind =, simp]
theorem mem_mapMatrix_iff_bvpos {s : String} {nfa : NFA} {startPos : Pos s}
    (state : Fin nfa.size) (bp : BVPos startPos) (matrix : BitMatrix nfa.size (startPos.remainingBytes + 1)) :
    (state, bp.current) ∈ mapMatrix matrix ↔ matrix.get state bp.index := by
  rw [mem_mapMatrix_iff]
  constructor
  · intro ⟨le, h⟩
    rw [BVPos.index_eq_of_le le bp.le] at h
    simpa using h
  · intro h
    exact ⟨bp.le, by simpa [BVPos.index_eq_of_le bp.le bp.le] using h⟩

theorem mapMatrix_subset_of_forall_get {s : String} {nfa : NFA} {startPos : Pos s}
    {m m' : BitMatrix nfa.size (startPos.remainingBytes + 1)}
    (h : ∀ (i : Fin nfa.size) (j : Fin (startPos.remainingBytes + 1)), m.get i j → m'.get i j) :
    mapMatrix m ⊆ mapMatrix m' := by
  intro p hp
  rw [mem_mapMatrix_iff] at hp ⊢
  obtain ⟨le, hp⟩ := hp
  refine ⟨le, ?_⟩
  exact h _ _ hp

/--
Interpret a stack as successive `captureNextAux` calls: the model explores the top entry fully,
then continues with the rest of the stack on failure.
-/
noncomputable def modelRunStack {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s)
  (visited : Finset (Fin nfa.size × Pos s)) (stack : List (StackEntry σ nfa startPos)) :
  Option σ.Update × Finset (Fin nfa.size × Pos s) :=
  match stack with
  | [] => (.none, visited)
  | ⟨update, state, pos⟩ :: stack' =>
    let x := Model.captureNextAux σ nfa wf visited update state pos.current
    match x with
    | (_, .some u, ⟨v, _⟩) => (.some u, v)
    | (_, .none, ⟨v, _⟩) => modelRunStack σ nfa wf startPos v stack'

@[simp, grind =]
theorem modelRunStack_nil {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s}
  {visited : Finset (Fin nfa.size × Pos s)} :
  modelRunStack σ nfa wf startPos visited [] = (.none, visited) := by
  simp [modelRunStack]

@[simp, grind =]
theorem modelRunStack_singleton {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s}
    {visited : Finset (Fin nfa.size × Pos s)} {update : σ.Update} {state : Fin nfa.size} {bp : BVPos startPos} :
    modelRunStack σ nfa wf startPos visited [⟨update, state, bp⟩] =
      (Model.captureNextAux σ nfa wf visited update state bp.current).2.map id (·.val) := by
  grind [modelRunStack]

theorem modelRunStack_cons_visited {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s}
    {visited : Finset (Fin nfa.size × Pos s)} {update : σ.Update} {state : Fin nfa.size} {bp : BVPos startPos}
    {stack' : List (StackEntry σ nfa startPos)}
    (hmem : (state, bp.current) ∈ visited) :
    modelRunStack σ nfa wf startPos visited (⟨update, state, bp⟩ :: stack') =
      modelRunStack σ nfa wf startPos visited stack' := by
  simp [modelRunStack, Model.captureNextAux_visited hmem]

theorem modelRunStack_cons_done {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s}
    {visited : Finset (Fin nfa.size × Pos s)} {update : σ.Update} {state : Fin nfa.size} {bp : BVPos startPos}
    {stack' : List (StackEntry σ nfa startPos)}
    (hmem : (state, bp.current) ∉ visited) (hn : nfa[state] = .done) :
    modelRunStack σ nfa wf startPos visited (⟨update, state, bp⟩ :: stack') =
      (.some update, insert (state, bp.current) visited) := by
  simp [modelRunStack, Model.captureNextAux_done hmem hn]

theorem modelRunStack_cons_pushNext {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s}
    {visited : Finset (Fin nfa.size × Pos s)} {update : σ.Update} {state : Fin nfa.size} {bp : BVPos startPos}
    {stack' : List (StackEntry σ nfa startPos)}
    (hmem : (state, bp.current) ∉ visited) (hn : nfa[state] ≠ .done) :
    modelRunStack σ nfa wf startPos visited (⟨update, state, bp⟩ :: stack') =
      modelRunStack σ nfa wf startPos (insert (state, bp.current) visited)
        (pushNext σ nfa wf startPos stack' update state bp) := by
  cases stack', update, state, bp using captureNextAux.pushNext.fun_cases' σ nfa wf startPos with
  | done => contradiction
  | fail stack' update state bp hn' =>
    rw [captureNextAux.pushNext.fail hn']
    simp [modelRunStack, Model.captureNextAux_fail hmem hn']
  | epsilon stack' update state bp state' hn' =>
    rw [captureNextAux.pushNext.epsilon hn']
    grind [modelRunStack, Model.captureNextAux_epsilon hmem hn']
  | split stack' update state bp state₁ state₂ hn' =>
    rw [captureNextAux.pushNext.split hn']
    conv =>
      lhs
      simp [modelRunStack]
    rw [Model.captureNextAux_split hmem hn']
    split_ifs with hsome
    · simp [modelRunStack, Option.isSome_iff_exists] at hsome ⊢
      obtain ⟨u, hu⟩ := hsome
      grind
    · simp only [Bool.not_eq_true] at hsome
      grind [modelRunStack, Model.captureNextAux_split hmem hn']
  | save stack' update state bp offset state' hn' =>
    rw [captureNextAux.pushNext.save hn']
    grind [modelRunStack, Model.captureNextAux_save hmem hn']
  | anchor_pos stack' update state bp a state' hn' ht =>
    rw [captureNextAux.pushNext.anchor_pos hn' ht]
    grind [modelRunStack, Model.captureNextAux_anchor_pos hmem hn' ht]
  | anchor_neg stack' update state bp a state' hn' ht =>
    rw [captureNextAux.pushNext.anchor_neg hn' ht]
    simp [modelRunStack, Model.captureNextAux_anchor_neg hmem hn' ht]
  | char_pos stack' update state bp c state' hn' hne hc =>
    rw [captureNextAux.pushNext.char_pos hn' hne hc]
    have ne : bp.current ≠ s.endPos := by
      simpa [BVPos.ne_end_iff_current_ne_end] using hne
    have hc' : bp.current.get ne = c := by
      simpa [Regex.Data.BVPos.get_eq_get] using hc
    grind [modelRunStack, Model.captureNextAux_char_pos hmem hn' ne hc']
  | char_neg stack' update state bp c state' hn' h =>
    rw [captureNextAux.pushNext.char_neg hn' h]
    have h' : bp.current = s.endPos ∨ ∃ ne : bp.current ≠ s.endPos, bp.current.get ne ≠ c := by
      rcases h with heq | ⟨ne_bv, hc⟩
      · have : bp.current = s.endPos := by
          simpa [String.endBVPos, Regex.Data.BVPos.ext_iff] using congrArg Regex.Data.BVPos.current heq
        exact .inl this
      · exact .inr ⟨BVPos.ne_end_iff_current_ne_end.mp ne_bv, by simpa [Regex.Data.BVPos.get_eq_get] using hc⟩
    simp [modelRunStack, Model.captureNextAux_char_neg hmem hn' h']
  | sparse_pos stack' update state bp cs state' hn' hne hc =>
    rw [captureNextAux.pushNext.sparse_pos hn' hne hc]
    have ne : bp.current ≠ s.endPos := by
      simpa [BVPos.ne_end_iff_current_ne_end] using hne
    have hc' : bp.current.get ne ∈ cs := by
      simpa [Regex.Data.BVPos.get_eq_get] using hc
    grind [modelRunStack, Model.captureNextAux_sparse_pos hmem hn' ne hc']
  | sparse_neg stack' update state bp cs state' hn' h =>
    rw [captureNextAux.pushNext.sparse_neg hn' h]
    have h' : bp.current = s.endPos ∨ ∃ ne : bp.current ≠ s.endPos, bp.current.get ne ∉ cs := by
      rcases h with heq | ⟨ne_bv, hc⟩
      · have : bp.current = s.endPos := by
          simpa [String.endBVPos, Regex.Data.BVPos.ext_iff] using congrArg Regex.Data.BVPos.current heq
        exact .inl this
      · exact .inr ⟨BVPos.ne_end_iff_current_ne_end.mp ne_bv, by simpa [Regex.Data.BVPos.get_eq_get] using hc⟩
    simp [modelRunStack, Model.captureNextAux_sparse_neg hmem hn' h']

end Regex.Backtracker.Model

namespace Regex.Backtracker

open Regex.Backtracker.Model (mapMatrix mapMatrix_set mem_mapMatrix_iff_bvpos modelRunStack modelRunStack_nil
  modelRunStack_singleton modelRunStack_cons_visited modelRunStack_cons_done
  modelRunStack_cons_pushNext)

theorem captureNextAux_refinesModelStack {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed}
    {startPos : Pos s} (visited : BitMatrix nfa.size (startPos.remainingBytes + 1))
    (stack : List (StackEntry σ nfa startPos)) :
    modelRunStack σ nfa wf startPos (mapMatrix visited) stack =
      (captureNextAux σ nfa wf startPos visited stack).map id mapMatrix := by
  induction visited, stack using captureNextAuxRecOn σ nfa wf startPos with
  | base visited =>
    simp [captureNextAux_base, modelRunStack_nil]
  | visited visited update state bp stack' mem ih =>
    have hmem : (state, bp.current) ∈ mapMatrix visited := mem_mapMatrix_iff_bvpos state bp visited |>.mpr mem
    simpa [captureNextAux_visited mem, modelRunStack_cons_visited hmem] using ih
  | done visited update state bp stack' mem hn =>
    have hmem : (state, bp.current) ∉ mapMatrix visited := by
      intro h
      exact mem (mem_mapMatrix_iff_bvpos state bp visited |>.mp h)
    simp [captureNextAux_done mem hn, mapMatrix_set, modelRunStack_cons_done hmem hn]
  | next visited update state bp stack' mem hn ih =>
    have hmem : (state, bp.current) ∉ mapMatrix visited := by
      intro h
      exact mem (mem_mapMatrix_iff_bvpos state bp visited |>.mp h)
    simpa [captureNextAux_next mem hn, mapMatrix_set, modelRunStack_cons_pushNext hmem hn] using ih

theorem captureNextAux_refinesModel {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed}
    {startPos : Pos s} (visited : BitMatrix nfa.size (startPos.remainingBytes + 1))
    (update : σ.Update) (state : Fin nfa.size) (bp : BVPos startPos) :
    (captureNextAux σ nfa wf startPos visited [⟨update, state, bp⟩]).map id mapMatrix =
      (Model.captureNextAux σ nfa wf (mapMatrix visited) update state bp.current).2.map id (·.val) := by
  have hmain := @captureNextAux_refinesModelStack s σ nfa wf startPos visited [⟨update, state, bp⟩]
  rw [modelRunStack_singleton] at hmain
  exact hmain.symm

end Regex.Backtracker
