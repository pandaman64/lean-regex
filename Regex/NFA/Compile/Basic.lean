import Regex.Data.Expr
import Regex.NFA.Basic

import Batteries.Data.Array.Lemmas

open Regex.Data (Expr)

namespace Regex.NFA

def pushNode (nfa : NFA) (node : Node) :
  { nfa' : NFA // nfa.nodes.size < nfa'.nodes.size } :=
  let start := nfa.nodes.size
  let nodes := nfa.nodes.push node
  let nfa' : NFA := ⟨nodes, start⟩

  ⟨nfa', by simp [nodes]⟩

@[simp]
theorem pushNode_size {nfa : NFA} {node : Node} :
  (nfa.pushNode node).val.nodes.size = nfa.nodes.size + 1 := by
  simp [pushNode]

theorem pushNode_get_lt {nfa : NFA} {node : Node}
  (i : Nat) (h : i < nfa.nodes.size) :
  (nfa.pushNode node).val[i]'(Nat.lt_trans h (nfa.pushNode node).property) = nfa[i] := by
  simp [pushNode, get_eq_nodes_get]
  rw [Array.getElem_push_lt]

@[simp]
theorem pushNode_get_eq {nfa : NFA} {node : Node} :
  (nfa.pushNode node).val[nfa.nodes.size] = node := by
  simp [pushNode, get_eq_nodes_get]

theorem pushNode_get {nfa : NFA} {node : Node}
  (i : Nat) (h : i < (nfa.pushNode node).val.nodes.size) :
  (nfa.pushNode node).val[i]'h = if h' : i < nfa.nodes.size then nfa[i]'h' else node := by
  simp at h
  cases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h) with
  | inl lt => simp [lt, pushNode_get_lt _ lt]
  | inr eq => simp [eq]

@[simp]
theorem pushNode_start_eq {nfa : NFA} {node : Node} : (nfa.pushNode node).val.start = nfa.nodes.size := rfl

/--
  Compile a Regex and append the resulting nodes to the NFA. The nodes will transition to `next` on match.
-/
def pushRegex (nfa : NFA) (next : Nat) : Expr → { nfa' : NFA // nfa.nodes.size < nfa'.nodes.size }
  | .empty => nfa.pushNode .fail
  | .epsilon => nfa.pushNode (.epsilon next)
  | .char c => nfa.pushNode (.char c next)
  | .classes cs => nfa.pushNode (.sparse cs next)
  | .group index r =>
    -- push the closing save node first
    let nfa' := nfa.pushNode (.save (2 * index + 1) next)
    let nfa'' := nfa'.val.pushRegex nfa'.val.start r
    let nfa''' := nfa''.val.pushNode (.save (2 * index) nfa''.val.start)

    have property : nfa.nodes.size < nfa'''.val.nodes.size :=
      calc
        _ < _ := nfa'.property
        _ < _ := nfa''.property
        _ < _ := nfa'''.property

    ⟨nfa''', property⟩
  | .alternate r₁ r₂ =>
    -- TODO: it feels better to compile r₂ first to align with concat
    let nfa₁ := nfa.pushRegex next r₁
    let start₁ := nfa₁.val.start
    let nfa₂ := nfa₁.val.pushRegex next r₂
    let start₂ := nfa₂.val.start

    let split := Node.split start₁ start₂

    let nfa' := nfa₂.val.pushNode split
    have property : nfa.nodes.size < nfa'.val.nodes.size :=
      calc
        _ < _ := nfa₁.property
        _ < _ := nfa₂.property
        _ < _ := nfa'.property

    ⟨nfa', property⟩
  | .concat r₁ r₂ =>
    let nfa₂ := nfa.pushRegex next r₂
    let nfa₁ := nfa₂.val.pushRegex nfa₂.val.start r₁

    ⟨nfa₁, Nat.lt_trans nfa₂.property nfa₁.property⟩
  | .star r =>
    -- We need to generate a placeholder node first. We use `fail` for it because
    -- 1. We want to make sure `done` does not appear except at the first node.
    -- 2. variants without data are represented as a boxed integer so there is one less allocation.
    let placeholder := nfa.pushNode .fail
    -- FIXME: generated code used to keep `placeholder` alive, copying the array. Investigate again
    let compiled := placeholder.val.pushRegex nfa.nodes.size r

    -- Patch the placeholder node
    have isLt : nfa.nodes.size < compiled.val.nodes.size :=
      calc
        _ < _ := placeholder.property
        _ < _ := compiled.property

    let split := Node.split compiled.val.start next
    let patched := compiled.val.nodes.set ⟨nfa.nodes.size, isLt⟩ split

    let nfa' := ⟨patched, nfa.nodes.size⟩
    have property :=
      calc
        _ < _ := placeholder.property
        _ < _ := compiled.property
        _ = nfa'.nodes.size := by simp [patched]

    ⟨nfa', property⟩

def compile (r : Expr) : NFA := done.pushRegex 0 r

end NFA
