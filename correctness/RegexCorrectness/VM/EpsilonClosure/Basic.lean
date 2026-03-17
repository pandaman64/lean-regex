module

import all Regex.Data.SparseSet
import all Regex.NFA.Basic
import all Regex.VM
import Regex.Strategy
import all RegexCorrectness.VM.Path
import Mathlib.Tactic.DepRewrite

open Regex.Data (SparseSet Anchor Classes)
open Regex (NFA)
open Regex.NFA (Node)
open String (Pos)

namespace Regex.VM.εClosure

namespace pushNext

section

variable {s : String} {α : Type} {tracker : PosTracker s α} {nfa : NFA} {pos : Pos s} {node : Node} {inBounds : node.inBounds nfa.size} {update : α} {stack : εStack α nfa}

@[grind =>]
theorem epsilon {state' : Nat} (hn : node = .epsilon state') :
  pushNext tracker nfa pos node inBounds update stack = (update, ⟨state', by simp_all [Node.inBounds]⟩) :: stack := by
  grind [pushNext]

@[grind =>]
theorem split {state₁ state₂ : Nat} (hn : node = .split state₁ state₂) :
  pushNext tracker nfa pos node inBounds update stack = (update, ⟨state₁, by simp_all [Node.inBounds]⟩) :: (update, ⟨state₂, by simp_all [Node.inBounds]⟩) :: stack := by
  grind [pushNext]

@[grind =>]
theorem save {offset state' : Nat} (hn : node = .save offset state') :
  pushNext tracker nfa pos node inBounds update stack = (tracker.write update offset pos, ⟨state', by simp_all [Node.inBounds]⟩) :: stack := by
  grind [pushNext]

@[grind =>]
theorem anchor_pos {a : Anchor} {state' : Nat} (hn : node = .anchor a state') (ht : a.test pos) :
  pushNext tracker nfa pos node inBounds update stack = (update, ⟨state', by simp_all [Node.inBounds]⟩) :: stack := by
  grind [pushNext]

@[grind =>]
theorem anchor_neg {a : Anchor} {state' : Nat} (hn : node = .anchor a state') (ht : ¬a.test pos) :
  pushNext tracker nfa pos node inBounds update stack = stack := by
  grind [pushNext]

@[grind =>]
theorem done (hn : node = .done) :
  pushNext tracker nfa pos node inBounds update stack = stack := by
  grind [pushNext]

@[grind =>]
theorem fail (hn : node = .fail) :
  pushNext tracker nfa pos node inBounds update stack = stack := by
  grind [pushNext]

@[grind =>]
theorem char {c : Char} {state' : Nat} (hn : node = .char c state') :
  pushNext tracker nfa pos node inBounds update stack = stack := by
  grind [pushNext]

@[grind =>]
theorem sparse {cs : Classes} {state' : Nat} (hn : node = .sparse cs state') :
  pushNext tracker nfa pos node inBounds update stack = stack := by
  grind [pushNext]

end

theorem fun_cases' {s : String} {α : Type} (nfa : NFA) (pos : Pos s)
  {motive : (node : Node) → node.inBounds nfa.size → α → εStack α nfa → Prop}
  (epsilon : ∀ (update : α) (stack : εStack α nfa) (state' : Nat) (inBounds : (Node.epsilon state').inBounds nfa.size),
    motive (Node.epsilon state') inBounds update stack)
  (split : ∀ (update : α) (stack : εStack α nfa) (state₁ state₂ : Nat) (inBounds : (Node.split state₁ state₂).inBounds nfa.size),
    motive (Node.split state₁ state₂) inBounds update stack)
  (save : ∀ (update : α) (stack : εStack α nfa) (offset state' : Nat) (inBounds : (Node.save offset state').inBounds nfa.size),
    motive (Node.save offset state') inBounds update stack)
  (anchor_pos : ∀ (update : α) (stack : εStack α nfa) (a : Anchor) (state' : Nat) (inBounds : (Node.anchor a state').inBounds nfa.size),
    a.test pos →
    motive (Node.anchor a state') inBounds update stack)
  (anchor_neg : ∀ (update : α) (stack : εStack α nfa) (a : Anchor) (state' : Nat) (inBounds : (Node.anchor a state').inBounds nfa.size),
    ¬a.test pos →
    motive (Node.anchor a state') inBounds update stack)
  (done : ∀ (update : α) (stack : εStack α nfa) (inBounds : Node.done.inBounds nfa.size),
    motive Node.done inBounds update stack)
  (fail : ∀ (update : α) (stack : εStack α nfa) (inBounds : Node.fail.inBounds nfa.size),
    motive Node.fail inBounds update stack)
  (char : ∀ (update : α) (stack : εStack α nfa) (c : Char) (state' : Nat) (inBounds : (Node.char c state').inBounds nfa.size),
    motive (Node.char c state') inBounds update stack)
  (sparse : ∀ (update : α) (stack : εStack α nfa) (cs : Classes) (state' : Nat) (inBounds : (Node.sparse cs state').inBounds nfa.size),
    motive (Node.sparse cs state') inBounds update stack) :
  ∀ (node : Node) (inBounds : node.inBounds nfa.size) (update : α) (stack : εStack α nfa),
    motive node inBounds update stack :=
  fun node inBounds update stack =>
    match node with
    | .epsilon state' => epsilon update stack state' inBounds
    | .split state₁ state₂ => split update stack state₁ state₂ inBounds
    | .save offset state' => save update stack offset state' inBounds
    | .anchor a state' =>
      if ht : a.test pos then
        anchor_pos update stack a state' inBounds ht
      else
        anchor_neg update stack a state' inBounds ht
    | .done => done update stack inBounds
    | .fail => fail update stack inBounds
    | .char c state' => char update stack c state' inBounds
    | .sparse cs state' => sparse update stack cs state' inBounds

end pushNext

-- Cleaner version of the fuction induction principle
-- It's crucial to annotate the types of the arguments of the branches. Otherwise, Lean consumse
-- too much memory. See https://github.com/leanprover/lean4/issues/6753.
theorem induct' {s : String} {α : Type} (tracker : PosTracker s α) (nfa : NFA) (wf : nfa.WellFormed) (pos : Pos s)
  (motive : Option α → SearchState α nfa → εStack α nfa → Prop)
  (base : ∀ (matched : Option α) (next : SearchState α nfa), motive matched next [])
  (visited : ∀ (matched : Option α) (next : SearchState α nfa) (update : α) (state : Fin nfa.size) (stack' : εStack α nfa),
    state ∈ next.states →
    motive matched next stack' →
    motive matched next ((update, state) :: stack'))
  (not_visited : ∀ (matched : Option α) (next : SearchState α nfa) (update : α) (state : Fin nfa.size) (stack' : εStack α nfa)
    (hmem : state ∉ next.states),
    let node := nfa[state]
    let matched' := if node = Node.done then matched <|> some update else matched
    let states' := next.states.insert state hmem
    let updates' := if writeUpdate node = true then next.updates.set state update else next.updates
    motive matched' ⟨states', updates'⟩ (pushNext tracker nfa pos node (wf.inBounds state state.isLt) update stack') →
    motive matched next ((update, state) :: stack')) :
  ∀ (matched : Option α) (next : SearchState α nfa) (stack : εStack α nfa), motive matched next stack :=
  fun matched next stack =>
    induct tracker nfa wf pos motive base visited
      (fun matched update state stack' states updates hmem _ ih => by
        simp only [Node.isDone_def, decide_eq_true_eq] at ih
        exact not_visited matched ⟨states, updates⟩ update state stack' hmem ih)
      matched next stack

/-
Simplification lemmas for `εClosure`.
-/
section

variable {s : String} {α : Type} {tracker : PosTracker s α} {nfa : NFA} {wf : nfa.WellFormed} {pos : Pos s}
  {matched : Option α} {next : SearchState α nfa} {update : α} {state : Fin nfa.size} {stack' : εStack α nfa}

theorem base : εClosure tracker nfa wf pos matched next [] = (matched, next) := by
  simp [εClosure]

theorem visited (hmem : state ∈ next.states) :
  εClosure tracker nfa wf pos matched next ((update, state) :: stack') = εClosure tracker nfa wf pos matched next stack' := by
  grind [εClosure]

theorem not_visited (hmem : state ∉ next.states) :
  letI node := nfa[state]
  letI matched' := if node = Node.done then matched <|> some update else matched
  letI states' := next.states.insert state hmem
  letI updates' := if writeUpdate node = true then next.updates.set state update else next.updates
  εClosure tracker nfa wf pos matched next ((update, state) :: stack') =
  εClosure tracker nfa wf pos matched' ⟨states', updates'⟩ (pushNext tracker nfa pos node (wf.inBounds state state.isLt) update stack') := by
  grind [εClosure]

end

end Regex.VM.εClosure
