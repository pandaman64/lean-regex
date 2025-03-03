import Regex.Data.SparseSet
import Regex.NFA.Basic
import Regex.VM
import Regex.VM.Strategy
import RegexCorrectness.VM.Path

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

-- Cleaner version of the fuction induction principle
-- It's crucial to annotate the types of the arguments of the branches. Otherwise, Lean consumse
-- too much memory. See https://github.com/leanprover/lean4/issues/6753.
theorem εClosure.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (motive : Option σ.Update → SearchState σ nfa → εStack σ nfa → Prop)
  (base : ∀ (matched : Option σ.Update) (next : SearchState σ nfa), motive matched next [])
  (visited :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa),
    state ∈ next.states →
    motive matched next stack' →
    motive matched next ((update, state) :: stack'))
  (epsilon :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .epsilon state' →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates⟩;
    motive matched next' ((update, state') :: stack') →
    motive matched next ((update, state) :: stack'))
  (anchor_pos :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (anchor : Data.Anchor) (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .anchor anchor state' →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates⟩;
    anchor.test it →
    motive matched next' ((update, state') :: stack') →
    motive matched next ((update, state) :: stack'))
  (anchor_neg :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (anchor : Data.Anchor) (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .anchor anchor state' →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates⟩;
    ¬anchor.test it →
    motive matched next' stack' →
    motive matched next ((update, state) :: stack'))
  (split :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (state₁ : Fin nfa.nodes.size) (state₂ : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .split state₁ state₂ →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates⟩;
    motive matched next' ((update, state₁) :: (update, state₂) :: stack') →
    motive matched next ((update, state) :: stack'))
  (save :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (offset : Nat) (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .save offset state' →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates⟩;
    motive matched next' ((σ.write update offset it.pos, state') :: stack') →
    motive matched next ((update, state) :: stack'))
  (done :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa),
    state ∉ next.states → nfa[state] = .done →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates.set state update⟩;
    motive (matched <|> .some update) next' stack' →
    motive matched next ((update, state) :: stack'))
  (char :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (c : Char) (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .char c state' →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates.set state update⟩;
    motive matched next' stack' →
    motive matched next ((update, state) :: stack'))
  (sparse :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa) (cs : Data.Classes) (state' : Fin nfa.nodes.size),
    state ∉ next.states → nfa[state] = .sparse cs state' →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates.set state update⟩;
    motive matched next' stack' →
    motive matched next ((update, state) :: stack'))
  (fail :
    ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update)
      (state : Fin nfa.nodes.size) (stack' : εStack σ nfa),
    state ∉ next.states → nfa[state] = .fail →
    let next' : SearchState σ nfa := ⟨next.states.insert state, next.updates⟩;
    motive matched next' stack' →
    motive matched next ((update, state) :: stack')) :
  ∀ matched next stack, motive matched next stack := fun matched next stack =>
    εClosure.induct σ nfa wf it motive base visited
      (fun matched update state stack' states updates state' hn isLt mem ih =>
        epsilon matched ⟨states, updates⟩ update state stack' ⟨state', isLt⟩ mem hn ih)
      (fun matched update state stack' states updates anchor state' hn isLt test mem ih =>
        anchor_pos matched ⟨states, updates⟩ update state stack' anchor ⟨state', isLt⟩ mem hn test ih)
      (fun matched update state stack' states updates anchor state' hn isLt test mem ih =>
        anchor_neg matched ⟨states, updates⟩ update state stack' anchor ⟨state', isLt⟩ mem hn test ih)
      (fun matched update state stack' states updates state₁ state₂ hn isLt mem ih =>
        split matched ⟨states, updates⟩ update state stack' ⟨state₁, isLt.1⟩ ⟨state₂, isLt.2⟩ mem hn ih)
      (fun matched update state stack' states updates offset state' hn isLt mem ih =>
        save matched ⟨states, updates⟩ update state stack' offset ⟨state', isLt⟩ mem hn ih)
      (fun matched update state stack' states updates hn mem ih =>
        done matched ⟨states, updates⟩ update state stack' mem hn ih)
      (fun matched update state stack' states updates c state' hn mem ih =>
        char matched ⟨states, updates⟩ update state stack' c ⟨state', wf.inBounds' state hn⟩ mem hn ih)
      (fun matched update state stack' states updates cs state' hn mem ih =>
        sparse matched ⟨states, updates⟩ update state stack' cs ⟨state', wf.inBounds' state hn⟩ mem hn ih)
      (fun matched update state stack' states updates hn mem ih =>
        fail matched ⟨states, updates⟩ update state stack' mem hn ih)
      matched next stack

/-
Simplification lemmas for `εClosure`.
-/
section

variable {σ nfa wf it matched next}

@[simp]
theorem εClosure_base : εClosure σ nfa wf it matched next [] = (matched, next) := by
  simp [εClosure]

@[simp]
theorem εClosure_visited {update state stack'} (hmem : state ∈ next.states) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched next stack' := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]

@[simp]
theorem εClosure_epsilon {update state stack' state'} (hmem : state ∉ next.states) (hn : nfa[state] = .epsilon state') :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, state') :: stack') := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_anchor_pos {update state stack' anchor state'} (hmem : state ∉ next.states) (hn : nfa[state] = .anchor anchor state') (h : anchor.test it) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, state') :: stack') := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_anchor_neg {update state stack' anchor state'} (hmem : state ∉ next.states) (hn : nfa[state] = .anchor anchor state') (h : ¬anchor.test it) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates⟩ stack' := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_split {update state stack' state₁ state₂} (hmem : state ∉ next.states) (hn : nfa[state] = .split state₁ state₂) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((update, state₁) :: (update, state₂) :: stack') := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_save {update state stack' offset state'} (hmem : state ∉ next.states) (hn : nfa[state] = .save offset state') :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates⟩ ((σ.write update offset it.pos, state') :: stack') := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_done {update state stack'} (hmem : state ∉ next.states) (hn : nfa[state] = .done) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it (matched <|> .some update) ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_char {update state stack' c state'} (hmem : state ∉ next.states) (hn : nfa[state] = .char c state') :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_sparse {update state stack' cs state'} (hmem : state ∉ next.states) (hn : nfa[state] = .sparse cs state') :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates.set state update⟩ stack' := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure_fail {update state stack'} (hmem : state ∉ next.states) (hn : nfa[state] = .fail) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched ⟨next.states.insert state, next.updates⟩ stack' := by
  conv =>
    lhs
    unfold εClosure
    simp [hmem]
  split <;> simp_all

end

end Regex.VM
