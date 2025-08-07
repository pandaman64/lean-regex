import Regex.Data.SparseSet
import Regex.NFA.Basic
import Regex.VM
import RegexCorrectness.VM.Path

set_option autoImplicit false

open Regex.Data (SparseSet Anchor Classes)
open Regex (NFA)
open Regex.NFA (Node)
open String (Pos Iterator)

namespace Regex.VM.εClosure

namespace pushNext

section

variable {σ : Strategy} {nfa : NFA} {it : Iterator} {node : Node} {inBounds : node.inBounds nfa.nodes.size} {update : σ.Update} {stack : εStack σ nfa}

theorem epsilonFin {state' : Fin nfa.nodes.size} (hn : node = .epsilon state') :
  pushNext σ nfa it node inBounds update stack = (update, state') :: stack := by
  unfold pushNext
  split <;> simp_all

theorem epsilon {state' : Nat} (hn : node = .epsilon state') :
  pushNext σ nfa it node inBounds update stack = (update, ⟨state', by simp_all [Node.inBounds]⟩) :: stack := by
  rw [epsilonFin (state' := ⟨state', by simp_all [Node.inBounds]⟩) hn]

theorem splitFin {state₁ state₂ : Fin nfa.nodes.size} (hn : node = .split state₁ state₂) :
  pushNext σ nfa it node inBounds update stack = (update, state₁) :: (update, state₂) :: stack := by
  unfold pushNext
  split <;> simp_all

theorem split {state₁ state₂ : Nat} (hn : node = .split state₁ state₂) :
  pushNext σ nfa it node inBounds update stack = (update, ⟨state₁, by simp_all [Node.inBounds]⟩) :: (update, ⟨state₂, by simp_all [NFA.Node.inBounds]⟩) :: stack := by
  rw [splitFin (state₁ := ⟨state₁, by simp_all [NFA.Node.inBounds]⟩) (state₂ := ⟨state₂, by simp_all [NFA.Node.inBounds]⟩) hn]

theorem saveFin {offset : Nat} {state' : Fin nfa.nodes.size} (hn : node = .save offset state') :
  pushNext σ nfa it node inBounds update stack = (σ.write update offset it.pos, state') :: stack := by
  unfold pushNext
  split <;> simp_all

theorem save {offset state' : Nat} (hn : node = .save offset state') :
  pushNext σ nfa it node inBounds update stack = (σ.write update offset it.pos, ⟨state', by simp_all [Node.inBounds]⟩) :: stack := by
  rw [saveFin (offset := offset) (state' := ⟨state', by simp_all [Node.inBounds]⟩) hn]

theorem anchor_posFin {a : Anchor} {state' : Fin nfa.nodes.size} (hn : node = .anchor a state') (ht : a.test it) :
  pushNext σ nfa it node inBounds update stack = (update, state') :: stack := by
  unfold pushNext
  split <;> simp_all

theorem anchor_pos {a : Anchor} {state' : Nat} (hn : node = .anchor a state') (ht : a.test it) :
  pushNext σ nfa it node inBounds update stack = (update, ⟨state', by simp_all [Node.inBounds]⟩) :: stack := by
  rw [anchor_posFin (state' := ⟨state', by simp_all [Node.inBounds]⟩) hn ht]

theorem anchor_negFin {a : Anchor} {state' : Fin nfa.nodes.size} (hn : node = .anchor a state') (ht : ¬a.test it) :
  pushNext σ nfa it node inBounds update stack = stack := by
  unfold pushNext
  split <;> simp_all

theorem anchor_neg {a : Anchor} {state' : Nat} (hn : node = .anchor a state') (ht : ¬a.test it) :
  pushNext σ nfa it node inBounds update stack = stack := by
  rw [anchor_negFin (state' := ⟨state', by simp_all [Node.inBounds]⟩) hn ht]

theorem done (hn : node = .done) :
  pushNext σ nfa it node inBounds update stack = stack := by
  unfold pushNext
  split <;> simp_all

theorem fail (hn : node = .fail) :
  pushNext σ nfa it node inBounds update stack = stack := by
  unfold pushNext
  split <;> simp_all

theorem char {c : Char} {state' : Nat} (hn : node = .char c state') :
  pushNext σ nfa it node inBounds update stack = stack := by
  unfold pushNext
  split <;> simp_all

theorem sparse {cs : Classes} {state' : Nat} (hn : node = .sparse cs state') :
  pushNext σ nfa it node inBounds update stack = stack := by
  unfold pushNext
  split <;> simp_all

end

theorem fun_cases' (σ : Strategy) (nfa : NFA) (it : Iterator)
  {motive : (node : Node) → node.inBounds nfa.nodes.size → σ.Update → εStack σ nfa → Prop}
  (epsilon : ∀ (update : σ.Update) (stack : εStack σ nfa) (state' : Nat) (inBounds : (Node.epsilon state').inBounds nfa.nodes.size),
    motive (Node.epsilon state') inBounds update stack)
  (split : ∀ (update : σ.Update) (stack : εStack σ nfa) (state₁ state₂ : Nat) (inBounds : (Node.split state₁ state₂).inBounds nfa.nodes.size),
    motive (Node.split state₁ state₂) inBounds update stack)
  (save : ∀ (update : σ.Update) (stack : εStack σ nfa) (offset state' : Nat) (inBounds : (Node.save offset state').inBounds nfa.nodes.size),
    motive (Node.save offset state') inBounds update stack)
  (anchor_pos : ∀ (update : σ.Update) (stack : εStack σ nfa) (a : Anchor) (state' : Nat) (inBounds : (Node.anchor a state').inBounds nfa.nodes.size),
    a.test it →
    motive (Node.anchor a state') inBounds update stack)
  (anchor_neg : ∀ (update : σ.Update) (stack : εStack σ nfa) (a : Anchor) (state' : Nat) (inBounds : (Node.anchor a state').inBounds nfa.nodes.size),
    ¬a.test it →
    motive (Node.anchor a state') inBounds update stack)
  (done : ∀ (update : σ.Update) (stack : εStack σ nfa) (inBounds : Node.done.inBounds nfa.nodes.size),
    motive Node.done inBounds update stack)
  (fail : ∀ (update : σ.Update) (stack : εStack σ nfa) (inBounds : Node.fail.inBounds nfa.nodes.size),
    motive Node.fail inBounds update stack)
  (char : ∀ (update : σ.Update) (stack : εStack σ nfa) (c : Char) (state' : Nat) (inBounds : (Node.char c state').inBounds nfa.nodes.size),
    motive (Node.char c state') inBounds update stack)
  (sparse : ∀ (update : σ.Update) (stack : εStack σ nfa) (cs : Classes) (state' : Nat) (inBounds : (Node.sparse cs state').inBounds nfa.nodes.size),
    motive (Node.sparse cs state') inBounds update stack) :
  ∀ (node : Node) (inBounds : node.inBounds nfa.nodes.size) (update : σ.Update) (stack : εStack σ nfa),
    motive node inBounds update stack :=
  fun node inBounds update stack =>
    match node with
    | .epsilon state' => epsilon update stack state' inBounds
    | .split state₁ state₂ => split update stack state₁ state₂ inBounds
    | .save offset state' => save update stack offset state' inBounds
    | .anchor a state' =>
      if ht : a.test it then
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
theorem induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (motive : Option σ.Update → SearchState σ nfa → εStack σ nfa → Prop)
  (base : ∀ (matched : Option σ.Update) (next : SearchState σ nfa), motive matched next [])
  (visited : ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update) (state : Fin nfa.nodes.size) (stack' : εStack σ nfa),
    state ∈ next.states →
    motive matched next stack' →
    motive matched next ((update, state) :: stack'))
  (not_visited : ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (update : σ.Update) (state : Fin nfa.nodes.size) (stack' : εStack σ nfa)
    (hmem : state ∉ next.states),
    let node := nfa[state]
    let matched' := if node = Node.done then matched <|> some update else matched
    let states' := next.states.insert state hmem
    let updates' := if writeUpdate node = true then next.updates.set state update else next.updates
    motive matched' ⟨states', updates'⟩ (pushNext σ nfa it node (wf.inBounds state) update stack') →
    motive matched next ((update, state) :: stack')) :
  ∀ (matched : Option σ.Update) (next : SearchState σ nfa) (stack : εStack σ nfa), motive matched next stack :=
  fun matched next stack =>
    induct σ nfa wf it motive base visited
      (fun matched update state stack' states updates hmem _ ih => by
        simp only [Node.isDone_def, decide_eq_true_eq] at ih
        exact not_visited matched ⟨states, updates⟩ update state stack' hmem ih)
      matched next stack

/-
Simplification lemmas for `εClosure`.
-/
section

variable {σ : Strategy} {nfa : NFA} {wf : nfa.WellFormed} {it : Iterator} {matched : Option σ.Update} {next : SearchState σ nfa}
  {update : σ.Update} {state : Fin nfa.nodes.size} {stack' : εStack σ nfa}

theorem base : εClosure σ nfa wf it matched next [] = (matched, next) := by
  simp [εClosure]

theorem visited (hmem : state ∈ next.states) :
  εClosure σ nfa wf it matched next ((update, state) :: stack') = εClosure σ nfa wf it matched next stack' := by
  conv =>
    lhs
    simp [εClosure, hmem]

theorem not_visited (hmem : state ∉ next.states) :
  letI node := nfa[state]
  letI matched' := if node = Node.done then matched <|> some update else matched
  letI states' := next.states.insert state hmem
  letI updates' := if writeUpdate node = true then next.updates.set state update else next.updates
  εClosure σ nfa wf it matched next ((update, state) :: stack') =
  εClosure σ nfa wf it matched' ⟨states', updates'⟩ (pushNext σ nfa it node (wf.inBounds state) update stack') := by
  conv =>
    lhs
    simp only [εClosure, hmem, reduceDIte, Node.isDone_def, decide_eq_true_eq]

end


end Regex.VM.εClosure
