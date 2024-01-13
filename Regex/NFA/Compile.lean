import Regex.Lemmas
import Regex.Regex
import Regex.NFA.Basic

import Std.Data.Array.Lemmas

namespace NFA

def NFA.addNode (nfa : NFA) (node : Node) :
  { nfa' : NFA // nfa.nodes.size ≤ nfa'.nodes.size } :=
  have isLt : nfa.nodes.size < (nfa.nodes.push node).size := by
    simp [Array.size_push]
  let start := nfa.nodes.size
  let nfa' : NFA := ⟨nfa.nodes.push node, ⟨start, isLt⟩⟩

  have property : nfa.nodes.size ≤ nfa'.nodes.size := by
    simp
    exact Nat.le_succ _

  ⟨nfa', property⟩

theorem NFA.lt_size_addNode {nfa : NFA} {node : Node} :
  nfa.nodes.size < (nfa.addNode node).val.nodes.size := (nfa.addNode node).val.start.isLt

theorem NFA.get_lt_addNode {nfa : NFA} {node : Node} (h : i < nfa.nodes.size) :
  (nfa.addNode node).val[i]'(Nat.lt_trans h lt_size_addNode) = nfa[i] :=
  Array.get_push_lt _ _ _ h

@[simp]
theorem NFA.get?_addNode {nfa : NFA} {node : Node} :
  (nfa.addNode node).val[(nfa.addNode node).val.start.val]? = some node := by
  simp [NFA.addNode]
  apply Array.get?_push_eq

@[simp]
theorem NFA.get_addNode {nfa : NFA} {node : Node} :
  (nfa.addNode node).val[(nfa.addNode node).val.start.val] = node := by
  simp [NFA.addNode]
  apply Array.get_push_eq

@[simp]
theorem NFA.get_addNode' {nfa : NFA} {node : Node} :
  (nfa.addNode node).val[nfa.nodes.size]'(NFA.lt_size_addNode) = node := by
  have : nfa.nodes.size = (nfa.addNode node).val.start.val := by
    simp [NFA.addNode]
  simp [this]

theorem NFA.start_addNode {nfa : NFA} {node : Node} {result : { nfa' : NFA // nfa.nodes.size ≤ nfa'.nodes.size }}
  (eq : nfa.addNode node = result) :
  result.val.start.val = nfa.nodes.size := by
  rw [←eq]
  simp [NFA.addNode]

@[export lean_regex_nfa_compile_regex]
def compile (r : Regex) : NFA :=
  let result := loop r 0 init
  result.val
where
  init : NFA := ⟨#[.done], ⟨0, Nat.zero_lt_succ _⟩⟩
  /--
    The main loop of the compilation.

    It compiles the given regex into nodes that transitions to `next` on match.
    Returned NFA contains the compiled nodes at the end and starts at the node
    corresponding to the given regex.
  -/
  loop (r : Regex) (next : Nat) (nfa : NFA) : { nfa' // nfa.nodes.size ≤ nfa'.nodes.size } := match r with
  | .empty => nfa.addNode .fail
  | .epsilon => nfa.addNode (.epsilon next)
  | .char c => nfa.addNode (.char c next)
  | .alternate r₁ r₂ =>
    -- TODO: it feels better to compile r₂ first to align with concat
    let nfa₁ := loop r₁ next nfa
    let start₁ := nfa₁.val.start
    let nfa₂ := loop r₂ next nfa₁
    let start₂ := nfa₂.val.start
    let nfa' := nfa₂.val.addNode (.split start₁ start₂)

    have property : nfa.nodes.size ≤ nfa'.val.nodes.size :=
      -- calc nfa
      --   _ ≤ nfa₁.val := nfa₁.property
      --   _ ≤ nfa₂.val := nfa₂.property
      --   _ ≤ nfa' := nfa'.property
      calc nfa.nodes.size
        _ ≤ nfa₁.val.nodes.size := nfa₁.property
        _ ≤ nfa₂.val.nodes.size := nfa₂.property
        _ ≤ nfa'.val.nodes.size := nfa'.property

    ⟨nfa', property⟩
  | .concat r₁ r₂ =>
    let nfa₂ := loop r₂ next nfa
    let nfa₁ := loop r₁ nfa₂.val.start nfa₂

    have property : nfa.nodes.size ≤ nfa₁.val.nodes.size :=
      -- calc nfa
      --   _ ≤ nfa₂.val := nfa₂.property
      --   _ ≤ nfa₁.val := nfa₁.property
      calc nfa.nodes.size
        _ ≤ nfa₂.val.nodes.size := nfa₂.property
        _ ≤ nfa₁.val.nodes.size := nfa₁.property

    ⟨nfa₁, property⟩
  | .star r =>
    -- We need to generate a placeholder node first. We use `fail` for it because
    -- 1. We'll use the fact that `fail` is a minimal element when strengthening induction hypotheis;
    -- 2. We want to make sure `done` does not appear except at the first node.
    -- 3. variants without data are represented as a boxed integer so there is one less allocation.
    -- TODO: check generated code
    let nfa' := nfa.addNode .fail
    let start := nfa'.val.start
    let nfa'' := loop r start nfa'

    have property : nfa.nodes.size ≤ nfa''.val.nodes.size :=
      -- calc nfa
      --   _ ≤ nfa'.val := nfa'.property
      --   _ ≤ nfa''.val := nfa''.property
      calc nfa.nodes.size
        _ ≤ nfa'.val.nodes.size := nfa'.property
        _ ≤ nfa''.val.nodes.size := nfa''.property
    have isLt : start.val < nfa''.val.nodes.size :=
      Nat.lt_of_lt_of_le nfa'.val.start.isLt nfa''.property

    -- Patch the placeholder node
    let target := nfa''.val.start
    let nodes''' := nfa''.val.nodes.set ⟨start.val, isLt⟩ (.split target next)

    -- TODO: maybe I should have used Fin.cast
    have eq_size : nodes'''.size = nfa''.val.nodes.size := by simp
    have isLt' : start.val < nodes'''.size := eq_size ▸ isLt
    let nfa''' := ⟨nodes''', ⟨start.val, isLt'⟩⟩

    have property' : nfa.nodes.size ≤ nfa'''.nodes.size := by
      simp
      exact property
      -- intro i h

      -- have le_size : nfa.nodes.size ≤ nfa''.val.nodes.size := NFA.le_size_of_le property
      -- have h₂ : i < nodes'''.size := Nat.lt_of_lt_of_le h (eq_size ▸ property)
      -- exists h₂

      -- have eq : nfa'''[i] = nfa''.val[i]'(Nat.lt_of_lt_of_le h le_size) := by
      --   apply Array.get_set_ne
      --   exact (Nat.ne_of_gt h)
      -- rw [eq]
      -- exact (property i _).2

    ⟨nfa''', property'⟩

end NFA
