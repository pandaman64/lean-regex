import Regex.Backtracker

set_option autoImplicit false

open Regex.Data (BoundedIterator)

namespace Regex.Backtracker

theorem captureNextAux.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx maxIdx : Nat)
  (motive : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx) → List (StackEntry σ nfa startIdx maxIdx) → Prop)
  (base : ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)), motive visited [])
  (visited :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    visited.get state (it.index' eq) →
    motive visited stack' →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (done :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    nfa[state] = NFA.Node.done →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (fail :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    nfa[state] = NFA.Node.fail →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (epsilon :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.epsilon state' →
    motive visited' (⟨update, state', it, eq⟩ :: stack') →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (split :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (state₁ state₂ : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.split state₁ state₂ →
    motive visited' (⟨update, state₁, it, eq⟩ :: ⟨update, state₂, it, eq⟩ :: stack') →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (save :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (offset : Nat) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.save offset state' →
    let update' := σ.write update offset it.pos;
    motive visited' (⟨update', state', it, eq⟩ :: stack') →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (anchor_pos :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (a : Data.Anchor) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.anchor a state' →
    Data.Anchor.test it.it a →
    motive visited' (⟨update, state', it, eq⟩ :: stack') →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (anchor_neg :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (a : Data.Anchor) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.anchor a state' →
    ¬Data.Anchor.test it.it a →
    motive visited' stack' →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (char_pos :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.char c state' →
    (h : it.hasNext) →
    it.curr h = c →
    motive visited' (⟨update, state', it.next h, eq⟩ :: stack') →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (char_neg :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.char c state' →
    (h : it.hasNext) →
    ¬it.curr h = c →
    motive visited' stack' →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (char_end :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (c : Char) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.char c state' →
    ¬it.hasNext →
    motive visited' stack' →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (sparse_pos :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.sparse cs state' →
    (h : it.hasNext) →
    it.curr h ∈ cs →
    motive visited' (⟨update, state', it.next h, eq⟩ :: stack') →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (sparse_neg :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.sparse cs state' →
    (h : it.hasNext) →
    ¬it.curr h ∈ cs →
    motive visited' stack' →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (sparse_end :
    ∀ (visited : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (update : σ.Update)
      (state : Fin nfa.nodes.size) (it : BoundedIterator startIdx) (eq : it.maxIdx = maxIdx)
      (stack' : List (StackEntry σ nfa startIdx maxIdx)),
    ¬visited.get state (it.index' eq) →
    let visited' := visited.set state (it.index' eq);
    ∀ (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    nfa[state] = NFA.Node.sparse cs state' →
    ¬it.hasNext →
    motive visited' stack' →
    motive visited (⟨update, state, it, eq⟩ :: stack'))
  (matrix : BitMatrix nfa.nodes.size (maxIdx + 1 - startIdx)) (stack : List (StackEntry σ nfa startIdx maxIdx)) :
  motive matrix stack :=
  captureNextAux.induct σ nfa wf startIdx maxIdx motive base visited
    (fun visited update state it eq stack' mem _ hn =>
      done visited update state it eq stack' mem hn)
    (fun visited update state it eq stack' mem _ hn =>
      fail visited update state it eq stack' mem hn)
    (fun visited update state it eq stack' mem _ state' hn isLt ih =>
      epsilon visited update state it eq stack' mem ⟨state', isLt⟩ hn ih)
    (fun visited update state it eq stack' mem _ state₁ state₂ hn isLt ih =>
      split visited update state it eq stack' mem ⟨state₁, isLt.1⟩ ⟨state₂, isLt.2⟩ hn ih)
    (fun visited update state it eq stack' mem _ offset state' hn isLt ih =>
      save visited update state it eq stack' mem offset ⟨state', isLt⟩ hn ih)
    (fun visited update state it eq stack' mem _ a state' hn isLt ih =>
      anchor_pos visited update state it eq stack' mem a ⟨state', isLt⟩ hn ih)
    (fun visited update state it eq stack' mem _ a state' hn isLt ih =>
      anchor_neg visited update state it eq stack' mem a ⟨state', isLt⟩ hn ih)
    (fun visited update state it eq stack' mem _ state' isLt h hn ih =>
      char_pos visited update state it eq stack' mem (it.curr h) ⟨state', isLt⟩ hn h rfl ih)
    (fun visited update state it eq stack' mem _ c state' hn isLt h ne ih =>
      char_neg visited update state it eq stack' mem c ⟨state', isLt⟩ hn h ne ih)
    (fun visited update state it eq stack' mem _ c state' hn isLt h ih =>
      char_end visited update state it eq stack' mem c ⟨state', isLt⟩ hn h ih)
    (fun visited update state it eq stack' mem _ cs state' hn isLt h ih =>
      sparse_pos visited update state it eq stack' mem cs ⟨state', isLt⟩ hn h ih)
    (fun visited update state it eq stack' mem _ cs state' hn isLt h ih =>
      sparse_neg visited update state it eq stack' mem cs ⟨state', isLt⟩ hn h ih)
    (fun visited update state it eq stack' mem _ cs state' hn isLt h ih =>
      sparse_end visited update state it eq stack' mem cs ⟨state', isLt⟩ hn h ih)
    matrix stack

/-
Simplification lemmas for `captureNextAux`.
-/
section

variable {σ nfa wf startIdx maxIdx visited}

theorem captureNextAux_base :
  captureNextAux σ nfa wf startIdx maxIdx visited [] = (.none, visited) := by
  simp [captureNextAux]

theorem captureNextAux_visited {update state it eq stack'} (mem : visited.get state (it.index' eq)) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') = captureNextAux σ nfa wf startIdx maxIdx visited stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]

theorem captureNextAux_done {update state it eq stack'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .done) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') = (.some update, visited.set state (it.index' eq)) := by
  simp at hn
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_fail {update state it eq stack'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .fail) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') = (.none, visited.set state (it.index' eq)) := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_epsilon {update state it eq stack' state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .epsilon state') :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) (⟨update, state', it, eq⟩ :: stack') := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_split {update state it eq stack' state₁ state₂} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .split state₁ state₂) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) (⟨update, state₁, it, eq⟩ :: ⟨update, state₂, it, eq⟩ :: stack') := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_save {update state it eq stack' offset state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .save offset state') :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) (⟨σ.write update offset it.pos, state', it, eq⟩ :: stack') := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_anchor_pos {update state it eq stack' a state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .anchor a state') (h : Data.Anchor.test it.it a) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) (⟨update, state', it, eq⟩ :: stack') := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_anchor_neg {update state it eq stack' a state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .anchor a state') (h : ¬Data.Anchor.test it.it a) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_char_pos {update state it eq stack' c state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .char c state') (h : it.hasNext) (hc : it.curr h = c) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) (⟨update, state', it.next h, eq⟩ :: stack') := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_char_neg {update state it eq stack' c state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .char c state') (h : it.hasNext) (hc : ¬it.curr h = c) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_char_end {update state it eq stack' c state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .char c state') (h : ¬it.hasNext) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_sparse_pos {update state it eq stack' cs state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .sparse cs state') (h : it.hasNext) (hc : it.curr h ∈ cs) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) (⟨update, state', it.next h, eq⟩ :: stack') := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_sparse_neg {update state it eq stack' cs state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .sparse cs state') (h : it.hasNext) (hc : ¬it.curr h ∈ cs) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

theorem captureNextAux_sparse_end {update state it eq stack' cs state'} (mem : ¬visited.get state (it.index' eq)) (hn : nfa[state] = .sparse cs state') (h : ¬it.hasNext) :
  captureNextAux σ nfa wf startIdx maxIdx visited (⟨update, state, it, eq⟩ :: stack') =
  captureNextAux σ nfa wf startIdx maxIdx (visited.set state (it.index' eq)) stack' := by
  conv =>
    lhs
    unfold captureNextAux
    simp [mem]
  split <;> simp_all

end

theorem captureNext.go.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (startIdx : Nat)
  (motive : (bit : BoundedIterator startIdx) → BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx) → Prop)
  (found : ∀ (bit : BoundedIterator startIdx) (visited : BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx)) (update : σ.Update) (visited' : BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx)),
    captureNextAux σ nfa wf startIdx bit.maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] = (.some update, visited') →
    motive bit visited)
  (not_found_next : ∀ (bit : BoundedIterator startIdx) (visited visited' : BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx)),
    captureNextAux σ nfa wf startIdx bit.maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] = (.none, visited') →
    (h : bit.hasNext) →
    (ih : motive (bit.next h) visited') →
    motive bit visited)
  (not_found_end : ∀ (bit : BoundedIterator startIdx) (visited visited' : BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx)),
    captureNextAux σ nfa wf startIdx bit.maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] = (.none, visited') →
    ¬bit.hasNext →
    motive bit visited)
  (bit : BoundedIterator startIdx) (visited : BitMatrix nfa.nodes.size (bit.maxIdx + 1 - startIdx)) :
  motive bit visited :=
  captureNext.go.induct σ nfa wf startIdx motive
    found
    (fun bit visited visited' hres h _ ih => not_found_next bit visited visited' hres h ih)
    not_found_end
    bit visited

/-
Simplification lemmas for `captureNext.go`.
-/
section

variable {σ nfa wf startIdx bit visited}

theorem captureNext.go_found {update visited'} (h : captureNextAux σ nfa wf startIdx bit.maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] = (.some update, visited')) :
  captureNext.go σ nfa wf startIdx bit visited = (.some update, visited') := by
  unfold captureNext.go
  split <;> simp_all

theorem captureNext.go_not_found_next {visited'} (h : captureNextAux σ nfa wf startIdx bit.maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] = (.none, visited')) (h' : bit.hasNext) :
  captureNext.go σ nfa wf startIdx bit visited = captureNext.go σ nfa wf startIdx (bit.next h') visited' := by
  conv =>
    lhs
    unfold captureNext.go
  split <;> simp_all

theorem captureNext.go_not_found_end {visited'} (h : captureNextAux σ nfa wf startIdx bit.maxIdx visited [⟨σ.empty, ⟨nfa.start, wf.start_lt⟩, bit, rfl⟩] = (.none, visited')) (h' : ¬bit.hasNext) :
  captureNext.go σ nfa wf startIdx bit visited = (.none, visited') := by
  unfold captureNext.go
  split <;> simp_all

end

/-
Simplification lemmas for `captureNext`.
-/
section

variable {σ nfa wf it}

theorem captureNext_le (le : it.pos ≤ it.toString.endPos) :
  captureNext σ nfa wf it = (captureNext.go σ nfa wf it.pos.byteIdx ⟨it, Nat.le_refl _, le⟩ (BitMatrix.zero _ _)).1 := by
  simp [captureNext, le]

theorem captureNext_not_le (h : ¬it.pos ≤ it.toString.endPos) :
  captureNext σ nfa wf it = .none := by
  simp [captureNext, h]

end

end Regex.Backtracker
