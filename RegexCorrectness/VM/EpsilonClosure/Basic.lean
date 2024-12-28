import Regex.Data.Array
import Regex.Data.SparseSet
import Regex.NFA.Basic
import Regex.VM

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

abbrev εStack' (nfa : NFA) := List (List (Nat × Pos) × Fin nfa.nodes.size)

/--
A version of εClosure traversal that tracks the updates to the capture groups.

As the NFA semantics use `List (Nat × Pos)` to represent the capture group updates, this
εClosure implementation also use it for verification. The actual VM implementation materializes the
updates as a `Buffer` for efficiency, and the correspondence will be proved in `Correspondence.lean`.
-/
def εClosure' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (next : SparseSet nfa.nodes.size) (matched : Option (List (Nat × Pos))) (updates : Vec (List (Nat × Pos)) nfa.nodes.size)
  (stack : εStack' nfa) :
  (SparseSet nfa.nodes.size × Option (List (Nat × Pos)) × Vec (List (Nat × Pos)) nfa.nodes.size) :=
  match stack with
  | [] => (next, matched, updates)
  | (update, state) :: stack' =>
    if state ∈ next then
      εClosure' nfa wf it next matched updates stack'
    else
      let next' := next.insert state
      match hn : nfa[state] with
      | .epsilon state' =>
        have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
        εClosure' nfa wf it next' matched updates ((update, ⟨state', isLt⟩) :: stack')
      | .split state₁ state₂ =>
        have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
        εClosure' nfa wf it next' matched updates ((update, ⟨state₁, isLt.1⟩) :: (update, ⟨state₂, isLt.2⟩):: stack')
      | .save offset state' =>
        have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
        let update' := update ++ [(offset, it.pos)]
        εClosure' nfa wf it next' matched updates ((update', ⟨state', isLt⟩) :: stack')
      | .done =>
        let matched' := matched <|> update
        let buffers' := updates.set state state.isLt update
        εClosure' nfa wf it next' matched' buffers' stack'
      | .char c state' =>
        let buffers' := updates.set state state.isLt update
        εClosure' nfa wf it next' matched buffers' stack'
      | .sparse cs state' =>
        let buffers' := updates.set state state.isLt update
        εClosure' nfa wf it next' matched buffers' stack'
      | .fail => εClosure' nfa wf it next' matched updates stack'
termination_by (next.measure, stack)

-- Tidied up version of the function induction
theorem εClosure'.induct' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator)
  (motive : SparseSet nfa.nodes.size → Option (List (Nat × Pos)) → Vec (List (Nat × Pos)) nfa.nodes.size → εStack' nfa → Prop)
  (base : ∀ next matched updates, motive next matched updates [])
  (visited : ∀ next matched updates update state stack',
    state ∈ next →
    motive next matched updates stack' →
    motive next matched updates ((update, state) :: stack'))
  (epsilon : ∀ next matched updates update state stack' state',
    state ∉ next → nfa[state] = .epsilon state' → motive (next.insert state) matched updates ((update, state') :: stack') →
    motive next matched updates ((update, state) :: stack'))
  (split : ∀ next matched updates update state stack' state₁ state₂,
    state ∉ next → nfa[state] = .split state₁ state₂ →
    motive (next.insert state) matched updates ((update, state₁) :: (update, state₂) :: stack') →
    motive next matched updates ((update, state) :: stack'))
  (save : ∀ next matched updates update state stack' offset state',
    state ∉ next → nfa[state] = .save offset state' →
    motive (next.insert state) matched updates ((update ++ [(offset, it.pos)], state') :: stack') →
    motive next matched updates ((update, state) :: stack'))
  (done : ∀ next matched updates update state stack',
    state ∉ next → nfa[state] = .done →
    motive (next.insert state) (matched <|> some update) (updates.set state state.isLt update) stack' →
    motive next matched updates ((update, state) :: stack'))
  (char : ∀ next matched updates update state stack' c state',
    state ∉ next → nfa[state] = .char c state' →
    motive (next.insert state) matched (updates.set state state.isLt update) stack' →
    motive next matched updates ((update, state) :: stack'))
  (sparse : ∀ next matched updates update state stack' cs state',
    state ∉ next → nfa[state] = .sparse cs state' →
    motive (next.insert state) matched (updates.set state state.isLt update) stack' →
    motive next matched updates ((update, state) :: stack'))
  (fail : ∀ next matched updates update state stack',
    state ∉ next → nfa[state] = .fail →
    motive (next.insert state) matched updates stack' →
    motive next matched updates ((update, state) :: stack')) :
  ∀ next matched updates stack, motive next matched updates stack := by
  refine εClosure'.induct nfa wf it motive base visited ?epsilon ?split ?save ?done ?char ?sparse ?fail
  case epsilon =>
    intro next matched updates update state stack' hmem next' state' hn isLt ih
    exact epsilon next matched updates update state stack' ⟨state', isLt⟩ hmem hn ih
  case split =>
    intro next matched updates update state stack' hmem next' state₁ state₂ hn isLt ih
    exact split next matched updates update state stack' ⟨state₁, isLt.1⟩ ⟨state₂, isLt.2⟩ hmem hn ih
  case save =>
    intro next matched updates update state stack' hmem next' offset state' hn isLt update' ih
    exact save next matched updates update state stack' offset ⟨state', isLt⟩ hmem hn ih
  case done =>
    intro next matched updates update state stack' hmem next' hn update' buffer' ih
    exact done next matched updates update state stack' hmem hn ih
  case char =>
    intro next matched updates update state stack' hmem next' c state' hn update' ih
    exact char next matched updates update state stack' c state' hmem hn ih
  case sparse =>
    intro next matched updates update state stack' hmem next' cs state' hn update' ih
    exact sparse next matched updates update state stack' cs state' hmem hn ih
  case fail =>
    intro next matched updates update state stack' hmem next' hn ih
    exact fail next matched updates update state stack' hmem hn ih

/-
Simplification lemmas for `εClosure'`.
-/
section

variable {nfa wf it next matched updates}

@[simp]
theorem εClosure'_base : εClosure' nfa wf it next matched updates [] = (next, matched, updates) := by
  simp [εClosure']

@[simp]
theorem εClosure'_visited {update state stack'} (hmem : state ∈ next) :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it next matched updates stack' := by
  simp [εClosure', hmem]

@[simp]
theorem εClosure'_epsilon {update state stack' state'} (hmem : state ∉ next) (hn : nfa[state] = .epsilon state') :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) matched updates ((update, state') :: stack') := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_split {update state stack' state₁ state₂} (hmem : state ∉ next) (hn : nfa[state] = .split state₁ state₂) :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) matched updates ((update, state₁) :: (update, state₂) :: stack') := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_save {update state stack' offset state'} (hmem : state ∉ next) (hn : nfa[state] = .save offset state') :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) matched updates ((update ++ [(offset, it.pos)], state') :: stack') := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_done {update state stack'} (hmem : state ∉ next) (hn : nfa[state] = .done) :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) (matched <|> some update) (updates.set state state.isLt update) stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_char {update state stack' c state'} (hmem : state ∉ next) (hn : nfa[state] = .char c state') :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) matched (updates.set state state.isLt update) stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_sparse {update state stack' cs state'} (hmem : state ∉ next) (hn : nfa[state] = .sparse cs state') :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) matched (updates.set state state.isLt update) stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

@[simp]
theorem εClosure'_fail {update state stack'} (hmem : state ∉ next) (hn : nfa[state] = .fail) :
  εClosure' nfa wf it next matched updates ((update, state) :: stack') = εClosure' nfa wf it (next.insert state) matched updates stack' := by
  conv =>
    lhs
    unfold εClosure'
    simp [hmem]
  split <;> simp_all

end

end Regex.VM
