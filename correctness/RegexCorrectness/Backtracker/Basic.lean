import Regex.Backtracker

set_option autoImplicit false

open Regex.Data (BitMatrix BoundedIterator)

namespace Regex.Backtracker

namespace captureNextAux.pushNext

variable {σ : Strategy} {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {stack : List (StackEntry σ nfa startIdx maxIdx)} {update : σ.Update} {state : Fin nfa.nodes.size} {it : BoundedIterator startIdx maxIdx}

theorem done (hn : nfa[state] = .done) : pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  simp at hn
  simp [hn]
  split <;> simp_all

theorem fail (hn : nfa[state] = .fail) : pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  split <;> simp_all

theorem epsilonFin {state' : Fin nfa.nodes.size} (hn : nfa[state] = .epsilon state') :
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, state', it⟩ :: stack := by
  unfold pushNext
  split <;> simp_all

theorem epsilon {state' : Nat} (hn : nfa[state] = .epsilon state') :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, ⟨state', isLt⟩, it⟩ :: stack := by
  rw [epsilonFin (state' := ⟨state', wf.inBounds' state hn⟩) hn]

theorem splitFin {state₁ state₂ : Fin nfa.nodes.size} (hn : nfa[state] = .split state₁ state₂) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, state₁, it⟩ :: ⟨update, state₂, it⟩ :: stack := by
  unfold pushNext
  split <;> simp_all

theorem split {state₁ state₂ : Nat} (hn : nfa[state] = .split state₁ state₂) :
  haveI isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, ⟨state₁, isLt.1⟩, it⟩ :: ⟨update, ⟨state₂, isLt.2⟩, it⟩ :: stack := by
  rw [splitFin (state₁ := ⟨state₁, (wf.inBounds' state hn).1⟩) (state₂ := ⟨state₂, (wf.inBounds' state hn).2⟩) hn]

theorem saveFin {offset : Nat} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .save offset state') :
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨σ.write update offset it.pos, state', it⟩ :: stack := by
  unfold pushNext
  split <;> simp_all

theorem save {offset state' : Nat} (hn : nfa[state] = .save offset state') :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨σ.write update offset it.pos, ⟨state', isLt⟩, it⟩ :: stack := by
  rw [saveFin (offset := offset) (state' := ⟨state', wf.inBounds' state hn⟩) hn]

theorem anchor_posFin {a : Data.Anchor} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .anchor a state') (h : Data.Anchor.test it.it a) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, state', it⟩ :: stack := by
  unfold pushNext
  split <;> simp_all

theorem anchor_pos {a : Data.Anchor} {state' : Nat} (hn : nfa[state] = .anchor a state') (h : Data.Anchor.test it.it a) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, ⟨state', isLt⟩, it⟩ :: stack := by
  rw [anchor_posFin (state' := ⟨state', wf.inBounds' state hn⟩) hn h]

theorem anchor_negFin {a : Data.Anchor} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .anchor a state') (h : ¬Data.Anchor.test it.it a) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  split <;> simp_all

theorem anchor_neg {a : Data.Anchor} {state' : Nat} (hn : nfa[state] = .anchor a state') (h : ¬Data.Anchor.test it.it a) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  rw [anchor_negFin (state' := ⟨state', wf.inBounds' state hn⟩) hn h]

theorem char_posFin {c : Char} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .char c state') (h : it.hasNext) (hc : it.curr h = c) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, state', it.next h⟩ :: stack := by
  unfold pushNext
  split <;> simp_all

theorem char_pos {c : Char} {state' : Nat} (hn : nfa[state] = .char c state') (h : it.hasNext) (hc : it.curr h = c) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, ⟨state', isLt⟩, it.next h⟩ :: stack := by
  rw [char_posFin (state' := ⟨state', wf.inBounds' state hn⟩) hn h hc]

theorem char_negFin {c : Char} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .char c state') (h : it.hasNext) (hc : ¬it.curr h = c) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  split <;> simp_all

theorem char_endFin {c : Char} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .char c state') (h : ¬it.hasNext) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  split <;> simp_all

theorem char_neg {c : Char} {state' : Nat} (hn : nfa[state] = .char c state') (h : ¬it.hasNext ∨ ∃ hnext : it.hasNext, ¬it.curr hnext = c) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  match h with
  | .inl h => rw [char_endFin (state' := ⟨state', wf.inBounds' state hn⟩) hn h]
  | .inr ⟨hnext, hc⟩ => rw [char_negFin (state' := ⟨state', wf.inBounds' state hn⟩) hn hnext hc]

theorem sparse_posFin {cs : Data.Classes} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .sparse cs state') (h : it.hasNext) (hc : it.curr h ∈ cs) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, state', it.next h⟩ :: stack := by
  unfold pushNext
  split <;> simp_all

theorem sparse_pos {cs : Data.Classes} {state' : Nat} (hn : nfa[state] = .sparse cs state') (h : it.hasNext) (hc : it.curr h ∈ cs) :
  haveI isLt : state' < nfa.nodes.size := wf.inBounds' state hn
  pushNext σ nfa wf startIdx maxIdx stack update state it = ⟨update, ⟨state', isLt⟩, it.next h⟩ :: stack := by
  rw [sparse_posFin (state' := ⟨state', wf.inBounds' state hn⟩) hn h hc]

theorem sparse_negFin {cs : Data.Classes} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .sparse cs state') (h : it.hasNext) (hc : ¬it.curr h ∈ cs) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  split <;> simp_all

theorem sparse_endFin {cs : Data.Classes} {state' : Fin nfa.nodes.size} (hn : nfa[state] = .sparse cs state') (h : ¬it.hasNext) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  unfold pushNext
  split <;> simp_all

theorem sparse_neg {cs : Data.Classes} {state' : Nat} (hn : nfa[state] = .sparse cs state') (h : ¬it.hasNext ∨ ∃ hnext : it.hasNext, ¬it.curr hnext ∈ cs) :
  pushNext σ nfa wf startIdx maxIdx stack update state it = stack := by
  match h with
  | .inl h => rw [sparse_endFin (state' := ⟨state', wf.inBounds' state hn⟩) hn h]
  | .inr ⟨hnext, hc⟩ => rw [sparse_negFin (state' := ⟨state', wf.inBounds' state hn⟩) hn hnext hc]

theorem fun_cases' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx maxIdx : Nat)
  {motive : List (StackEntry σ nfa startIdx maxIdx) → σ.Update → Fin nfa.nodes.size → BoundedIterator startIdx maxIdx → Prop}
  (done : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx),
    nfa[state] = .done → motive stack update state it)
  (fail : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx),
    nfa[state] = .fail → motive stack update state it)
  (epsilon : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (state' : Fin nfa.nodes.size),
    nfa[state] = .epsilon state' → motive stack update state it)
  (split : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (state₁ state₂ : Fin nfa.nodes.size),
    nfa[state] = .split state₁ state₂ → motive stack update state it)
  (save : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (offset : Nat) (state' : Fin nfa.nodes.size),
    nfa[state] = .save offset state' → motive stack update state it)
  (anchor_pos : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (a : Data.Anchor) (state' : Fin nfa.nodes.size),
    nfa[state] = .anchor a state' → a.test it.it → motive stack update state it)
  (anchor_neg : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (a : Data.Anchor) (state' : Fin nfa.nodes.size),
    nfa[state] = .anchor a state' → ¬a.test it.it → motive stack update state it)
  (char_pos : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = .char c state' → (h : it.hasNext) → it.curr h = c → motive stack update state it)
  (char_neg : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = .char c state' → (¬it.hasNext ∨ ∃ hnext : it.hasNext, ¬it.curr hnext = c) → motive stack update state it)
  (sparse_pos : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = .sparse cs state' → (h : it.hasNext) → it.curr h ∈ cs → motive stack update state it)
  (sparse_neg : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = .sparse cs state' → (¬it.hasNext ∨ ∃ hnext : it.hasNext, ¬it.curr hnext ∈ cs) → motive stack update state it)
  : ∀ (stack : List (StackEntry σ nfa startIdx maxIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx),
    motive stack update state it :=
  fun stack update state it =>
    match hn : nfa[state] with
    | .done => done stack update state it hn
    | .fail => fail stack update state it hn
    | .epsilon state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      epsilon stack update state it ⟨state', isLt⟩ hn
    | .split state₁ state₂ =>
      have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
      split stack update state it ⟨state₁, isLt.1⟩ ⟨state₂, isLt.2⟩ hn
    | .save offset state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      save stack update state it offset ⟨state', isLt⟩ hn
    | .anchor a state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      if ht : a.test it.it then
        anchor_pos stack update state it a ⟨state', isLt⟩ hn ht
      else
        anchor_neg stack update state it a ⟨state', isLt⟩ hn ht
    | .char c state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      if h : ∃ hnext : it.hasNext, it.curr hnext = c then
        char_pos stack update state it c ⟨state', isLt⟩ hn h.1 h.2
      else
        have h' : ¬it.hasNext ∨ ∃ hnext : it.hasNext, ¬it.curr hnext = c := by
          if hnext : it.hasNext then
            simp [hnext] at h
            exact .inr ⟨hnext, h⟩
          else
            exact .inl hnext
        char_neg stack update state it c ⟨state', isLt⟩ hn h'
    | .sparse cs state' =>
      have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
      if h : ∃ hnext : it.hasNext, it.curr hnext ∈ cs then
        sparse_pos stack update state it cs ⟨state', isLt⟩ hn h.1 h.2
      else
        have h' : ¬it.hasNext ∨ ∃ hnext : it.hasNext, ¬it.curr hnext ∈ cs := by
          if hnext : it.hasNext then
            simp [hnext] at h
            exact .inr ⟨hnext, h⟩
          else
            exact .inl hnext
        sparse_neg stack update state it cs ⟨state', isLt⟩ hn h'

end captureNextAux.pushNext

theorem captureNextAux.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx maxIdx : Nat)
  (motive : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx) → List (StackEntry σ nfa startIdx maxIdx) → Prop)
  (base : ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)), motive visited [])
  (visited : ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    visited.get state it.index →
    motive visited stack' →
    motive visited (⟨update, state, it⟩ :: stack'))
  (done : ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state it.index →
    nfa[state] = .done →
    motive visited (⟨update, state, it⟩ :: stack'))
  (next : ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update) (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx maxIdx) (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state it.index →
    nfa[state] ≠ .done →
    motive (visited.set state it.index) (pushNext σ nfa wf startIdx maxIdx stack' update state it) →
    motive visited (⟨update, state, it⟩ :: stack'))
  : ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (stack : List (StackEntry σ nfa startIdx maxIdx)), motive visited stack :=
  captureNextAux.induct σ nfa wf startIdx maxIdx motive
    base
    visited
    (fun visited update state it stack' hmem _ hn => done visited update state it stack' hmem hn)
    (fun visited update state it stack' hmem _ hn ih => next visited update state it stack' hmem hn ih)

/-
Simplification lemmas for `captureNextAux`.
-/
section

variable {σ nfa wf startIdx maxIdx visited}

theorem captureNextAux_base :
  captureNextAux σ nfa wf startIdx maxIdx visited [] = (.none, visited) := by
  simp [captureNextAux]

theorem captureNextAux_visited {update state it stack'} (mem : visited.get state it.index) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it⟩ :: stack') = captureNextAux σ nfa wf startIdx maxIdx visited stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]

theorem captureNextAux_done {update state it stack'} (mem : ¬visited.get state it.index) (hn : nfa[state] = .done) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it⟩ :: stack') = (.some update, visited.set state it.index) := by
  simp at hn
  conv =>
    lhs
    unfold captureNextAux
    simp [mem, hn]

theorem captureNextAux_next {update state it stack'} (mem : ¬visited.get state it.index) (hn : nfa[state] ≠ .done) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it⟩ :: stack') = captureNextAux σ nfa wf startIdx maxIdx (visited.set state it.index) (captureNextAux.pushNext σ nfa wf startIdx maxIdx stack' update state it) := by
  simp at hn
  conv =>
    lhs
    unfold captureNextAux
    simp [mem, hn]

end

theorem captureNext.go.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx maxIdx : Nat)
  (motive : (bit : BoundedIterator startIdx maxIdx) → BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx) → Prop)
  (found : ∀ (bit : BoundedIterator startIdx maxIdx) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update) (visited' : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)),
    captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = (.some update, visited') →
    motive bit visited)
  (not_found_next : ∀ (bit : BoundedIterator startIdx maxIdx) (visited visited' : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)),
    captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = (.none, visited') →
    (h : bit.hasNext) →
    (ih : motive (bit.next h) visited') →
    motive bit visited)
  (not_found_end : ∀ (bit : BoundedIterator startIdx maxIdx) (visited visited' : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)),
    captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = (.none, visited') →
    ¬bit.hasNext →
    motive bit visited)
  (bit : BoundedIterator startIdx maxIdx) (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) :
  motive bit visited :=
  captureNext.go.induct σ nfa wf startIdx maxIdx motive
    found
    (fun bit visited visited' hres h _ ih => not_found_next bit visited visited' hres h ih)
    not_found_end
    bit visited

/-
Simplification lemmas for `captureNext.go`.
-/
section

variable {σ nfa wf startIdx maxIdx bit visited}

theorem captureNext.go_found {update visited'} (h : captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = (.some update, visited')) :
  captureNext.go σ nfa wf startIdx maxIdx bit visited = .some update := by
  unfold captureNext.go
  split <;> simp_all

theorem captureNext.go_not_found_next {visited'} (h : captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = (.none, visited')) (h' : bit.hasNext) :
  captureNext.go σ nfa wf startIdx maxIdx bit visited = captureNext.go σ nfa wf startIdx maxIdx (bit.next h') visited' := by
  conv =>
    lhs
    unfold captureNext.go
  split <;> simp_all

theorem captureNext.go_not_found_end {visited'} (h : captureNextAux σ nfa wf startIdx maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit⟩] = (.none, visited')) (h' : ¬bit.hasNext) :
  captureNext.go σ nfa wf startIdx maxIdx bit visited = .none := by
  unfold captureNext.go
  split <;> simp_all

end

/-
Simplification lemmas for `captureNext`.
-/
section

variable {σ nfa wf it}

theorem captureNext_le (le : it.pos ≤ it.toString.endPos) :
  captureNext σ nfa wf it = (captureNext.go σ nfa wf it.pos.byteIdx it.toString.endPos.byteIdx ⟨it, Nat.le_refl _, le, rfl⟩ (BitMatrix.zero _ _)) := by
  simp [captureNext, le]

theorem captureNext_not_le (h : ¬it.pos ≤ it.toString.endPos) :
  captureNext σ nfa wf it = .none := by
  simp [captureNext, h]

end

end Regex.Backtracker
