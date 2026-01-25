import Regex.Backtracker
import Mathlib.Tactic.DepRewrite

set_option autoImplicit false

open Regex.Data (BitMatrix BVPos)
open String (Pos)

namespace Regex.Backtracker

namespace captureNextAux.pushNext

variable {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed}
  {startPos : Pos s} {stack : List (StackEntry σ nfa startPos)} {update : σ.Update} {state : Fin nfa.nodes.size} {pos : BVPos startPos}

theorem done (hn : nfa[state] = .done) : pushNext σ nfa wf startPos stack update state pos = stack := by
  rw! [pushNext, hn]
  rfl

theorem fail (hn : nfa[state] = .fail) : pushNext σ nfa wf startPos stack update state pos = stack := by
  rw! [pushNext, hn]
  rfl

theorem epsilon {state' : Nat} (hn : nfa[state] = .epsilon state') :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startPos stack update state pos = ⟨update, ⟨state', isLt⟩, pos⟩ :: stack := by
  rw! [pushNext, hn]
  rfl

theorem split {state₁ state₂ : Nat} (hn : nfa[state] = .split state₁ state₂) :
  haveI isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startPos stack update state pos = ⟨update, ⟨state₁, isLt.1⟩, pos⟩ :: ⟨update, ⟨state₂, isLt.2⟩, pos⟩ :: stack := by
  rw! [pushNext, hn]
  rfl

theorem saveFin {offset : Nat} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .save offset state') :
  pushNext σ nfa wf startPos stack update state pos = ⟨σ.write update offset pos.current, state', pos⟩ :: stack := by
  rw! [pushNext, hn]
  rfl

theorem save {offset state' : Nat} (hn : nfa[state] = .save offset state') :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startPos stack update state pos = ⟨σ.write update offset pos.current, ⟨state', isLt⟩, pos⟩ :: stack := by
  rw! [pushNext, hn]
  rfl

theorem anchor_pos {a : Data.Anchor} {state' : Nat} (hn : nfa[state] = .anchor a state') (h : Data.Anchor.test pos.current a) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startPos stack update state pos = ⟨update, ⟨state', isLt⟩, pos⟩ :: stack := by
  rw! [pushNext, hn]
  simp [h]

theorem anchor_neg {a : Data.Anchor} {state' : Nat} (hn : nfa[state] = .anchor a state') (h : ¬Data.Anchor.test pos.current a) :
  pushNext σ nfa wf startPos stack update state pos = stack := by
  rw! [pushNext, hn]
  simp [h]

theorem char_pos {c : Char} {state' : Nat} (hn : nfa[state] = .char c state') (h : pos ≠ s.endBVPos startPos) (hc : pos.get h = c) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startPos stack update state pos = ⟨update, ⟨state', isLt⟩, pos.next h⟩ :: stack := by
  rw! [pushNext, hn]
  simp [h, hc]

theorem char_neg {c : Char} {state' : Nat} (hn : nfa[state] = .char c state') (h : pos = s.endBVPos startPos ∨ ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ≠ c) :
  pushNext σ nfa wf startPos stack update state pos = stack := by
  rw! [pushNext, hn]
  match h with
  | .inl h => simp [h]
  | .inr ⟨ne, hc⟩ => simp [ne, hc]

theorem sparse_pos {cs : Data.Classes} {state' : Nat} (hn : nfa[state] = .sparse cs state') (h : pos ≠ s.endBVPos startPos) (hc : pos.get h ∈ cs) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startPos stack update state pos = ⟨update, ⟨state', isLt⟩, pos.next h⟩ :: stack := by
  rw! [pushNext, hn]
  simp [h, hc]

theorem sparse_neg {cs : Data.Classes} {state' : Nat} (hn : nfa[state] = .sparse cs state') (h : pos = s.endBVPos startPos ∨ ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ∉ cs) :
  pushNext σ nfa wf startPos stack update state pos = stack := by
  rw! [pushNext, hn]
  match h with
  | .inl h => simp [h]
  | .inr ⟨ne, hc⟩ => simp [ne, hc]

theorem fun_cases' (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s)
  {motive : List (StackEntry σ nfa startPos) → σ.Update → Fin nfa.nodes.size → BVPos startPos → Prop}
  (done : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos),
    nfa[state] = .done → motive stack update state pos)
  (fail : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos),
    nfa[state] = .fail → motive stack update state pos)
  (epsilon : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (state' : Fin nfa.nodes.size),
    nfa[state] = .epsilon state' → motive stack update state pos)
  (split : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (state₁ state₂ : Fin nfa.nodes.size),
    nfa[state] = .split state₁ state₂ → motive stack update state pos)
  (save : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (offset : Nat) (state' : Fin nfa.nodes.size),
    nfa[state] = .save offset state' → motive stack update state pos)
  (anchor_pos : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (a : Data.Anchor) (state' : Fin nfa.nodes.size),
    nfa[state] = .anchor a state' → a.test pos.current → motive stack update state pos)
  (anchor_neg : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (a : Data.Anchor) (state' : Fin nfa.nodes.size),
    nfa[state] = .anchor a state' → ¬a.test pos.current → motive stack update state pos)
  (char_pos : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = .char c state' → (h : pos ≠ s.endBVPos startPos) → pos.get h = c → motive stack update state pos)
  (char_neg : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = .char c state' → (pos = s.endBVPos startPos ∨ ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ≠ c) → motive stack update state pos)
  (sparse_pos : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = .sparse cs state' → (h : pos ≠ s.endBVPos startPos) → pos.get h ∈ cs → motive stack update state pos)
  (sparse_neg : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = .sparse cs state' → (pos = s.endBVPos startPos ∨ ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ∉ cs) → motive stack update state pos)
  : ∀ (stack : List (StackEntry σ nfa startPos)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos),
    motive stack update state pos :=
  fun stack update state pos =>
    match hn : nfa[state] with
    | .done => done stack update state pos hn
    | .fail => fail stack update state pos hn
    | .epsilon state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      epsilon stack update state pos ⟨state', isLt⟩ hn
    | .split state₁ state₂ =>
      have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
      split stack update state pos ⟨state₁, isLt.1⟩ ⟨state₂, isLt.2⟩ hn
    | .save offset state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      save stack update state pos offset ⟨state', isLt⟩ hn
    | .anchor a state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      if ht : a.test pos.current then
        anchor_pos stack update state pos a ⟨state', isLt⟩ hn ht
      else
        anchor_neg stack update state pos a ⟨state', isLt⟩ hn ht
    | .char c state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      if h : ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne = c then
        char_pos stack update state pos c ⟨state', isLt⟩ hn h.1 h.2
      else
        have h' : pos = s.endBVPos startPos ∨ ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ≠ c := by
          if ne : pos = s.endBVPos startPos then
            exact .inl ne
          else
            simp only [ne_eq, ne, not_false_eq_true, exists_true_left] at h
            exact .inr ⟨ne, h⟩
        char_neg stack update state pos c ⟨state', isLt⟩ hn h'
    | .sparse cs state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      if h : ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ∈ cs then
        sparse_pos stack update state pos cs ⟨state', isLt⟩ hn h.1 h.2
      else
        have h' : pos = s.endBVPos startPos ∨ ∃ ne : pos ≠ s.endBVPos startPos, pos.get ne ∉ cs := by
          if eq : pos = s.endBVPos startPos then
            exact .inl eq
          else
            simp only [ne_eq, eq, not_false_eq_true, exists_true_left] at h
            exact .inr ⟨eq, h⟩
        sparse_neg stack update state pos cs ⟨state', isLt⟩ hn h'

end captureNextAux.pushNext

theorem captureNextAux.induct' {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s)
  (motive : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1) → List (StackEntry σ nfa startPos) → Prop)
  (base : ∀ (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)), motive visited [])
  (visited : ∀ (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (stack' : List (StackEntry σ nfa startPos)),
    visited.get state pos.index →
    motive visited stack' →
    motive visited (⟨update, state, pos⟩ :: stack'))
  (done : ∀ (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (stack' : List (StackEntry σ nfa startPos)),
    ¬visited.get state pos.index →
    nfa[state] = .done →
    motive visited (⟨update, state, pos⟩ :: stack'))
  (next : ∀ (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (update : σ.Update) (state : Fin nfa.nodes.size) (pos : BVPos startPos) (stack' : List (StackEntry σ nfa startPos)),
    ¬visited.get state pos.index →
    nfa[state] ≠ .done →
    motive (visited.set state pos.index) (pushNext σ nfa wf startPos stack' update state pos) →
    motive visited (⟨update, state, pos⟩ :: stack'))
  : ∀ (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (stack : List (StackEntry σ nfa startPos)), motive visited stack :=
  captureNextAux.induct σ nfa wf startPos motive
    base
    visited
    (fun visited update state bvpos stack' hmem _ hn => done visited update state bvpos stack' hmem (by simpa using hn))
    (fun visited update state bvpos stack' hmem _ hn ih => next visited update state bvpos stack' hmem (by simpa using hn) ih)

/-
Simplification lemmas for `captureNextAux`.
-/
section

variable {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {startPos : Pos s} {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)}

theorem captureNextAux_base :
  captureNextAux σ nfa wf startPos visited [] = (.none, visited) := by
  simp [captureNextAux]

theorem captureNextAux_visited {update state pos stack'} (mem : visited.get state pos.index) :
  captureNextAux σ nfa wf startPos visited (⟨update, state, pos⟩ :: stack') = captureNextAux σ nfa wf startPos visited stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]

theorem captureNextAux_done {update state pos stack'} (mem : ¬visited.get state pos.index) (hn : nfa[state] = .done) :
  captureNextAux σ nfa wf startPos visited (⟨update, state, pos⟩ :: stack') = (.some update, visited.set state pos.index) := by
  simp at hn
  conv =>
    lhs
    unfold captureNextAux
    simp [mem, hn]

theorem captureNextAux_next {update state pos stack'} (mem : ¬visited.get state pos.index) (hn : nfa[state] ≠ .done) :
  captureNextAux σ nfa wf startPos visited (⟨update, state, pos⟩ :: stack') = captureNextAux σ nfa wf startPos (visited.set state pos.index) (captureNextAux.pushNext σ nfa wf startPos stack' update state pos) := by
  simp at hn
  conv =>
    lhs
    unfold captureNextAux
    simp [mem, hn]

end

theorem captureNext.go.induct' {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (startPos : Pos s)
  (motive : (pos : BVPos startPos) → BitMatrix nfa.nodes.size (startPos.remainingBytes + 1) → Prop)
  (found : ∀ (pos : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) (update : σ.Update) (visited' : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)),
    captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] = (.some update, visited') →
    motive pos visited)
  (not_found_next : ∀ (pos : BVPos startPos) (visited visited' : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)),
    captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] = (.none, visited') →
    (h : pos ≠ s.endBVPos startPos) →
    (ih : motive (pos.next h) visited') →
    motive pos visited)
  (not_found_end : ∀ (pos : BVPos startPos) (visited visited' : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)),
    captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] = (.none, visited') →
    ¬pos ≠ s.endBVPos startPos →
    motive pos visited)
  (pos : BVPos startPos) (visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)) :
  motive pos visited :=
  captureNext.go.induct σ nfa wf startPos motive
    found not_found_next not_found_end pos visited

/-
Simplification lemmas for `captureNext.go`.
-/
section

variable {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed}
  {startPos : Pos s} {visited : BitMatrix nfa.nodes.size (startPos.remainingBytes + 1)} {pos : BVPos startPos}

theorem captureNext.go_found {update visited'} (h : captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] = (.some update, visited')) :
  captureNext.go σ nfa wf startPos pos visited = .some update := by
  rw [captureNext.go, h]

theorem captureNext.go_not_found_next {visited'} (h : captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] = (.none, visited')) (h' : pos ≠ s.endBVPos startPos) :
  captureNext.go σ nfa wf startPos pos visited = captureNext.go σ nfa wf startPos (pos.next h') visited' := by
  rw [captureNext.go, h]
  simp [h']

theorem captureNext.go_not_found_end {visited'} (h : captureNextAux σ nfa wf startPos visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, pos⟩] = (.none, visited')) (h' : ¬pos ≠ s.endBVPos startPos) :
  captureNext.go σ nfa wf startPos pos visited = .none := by
  rw [captureNext.go, h]
  simp [h']

end

end Regex.Backtracker
