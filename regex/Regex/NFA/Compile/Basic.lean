import Regex.Data.Expr
import Regex.NFA.Basic

open Regex.Data (Expr)

namespace Regex.NFA

def pushNode (nfa : NFA) (node : Node) : NFA :=
  let start := nfa.nodes.size
  let nodes := nfa.nodes.push node
  ⟨nodes, start⟩

@[simp, grind =]
theorem pushNode_size {nfa : NFA} {node : Node} :
  (nfa.pushNode node).nodes.size = nfa.nodes.size + 1 := by
  simp [pushNode]

@[grind =]
theorem pushNode_get_lt {nfa : NFA} {node : Node}
  (i : Nat) (h : i < nfa.nodes.size) :
  (nfa.pushNode node)[i]'(Nat.lt_trans h (by simp only [pushNode_size, Nat.lt_add_one])) = nfa[i] := by
  simp [pushNode, get_eq_nodes_get]
  rw [Array.getElem_push_lt]

@[simp, grind =]
theorem pushNode_get_eq {nfa : NFA} {node : Node} :
  (nfa.pushNode node)[nfa.nodes.size] = node := by
  simp [pushNode, get_eq_nodes_get]

@[grind =]
theorem pushNode_get {nfa : NFA} {node : Node}
  (i : Nat) (h : i < (nfa.pushNode node).nodes.size) :
  (nfa.pushNode node)[i]'h = if h' : i < nfa.nodes.size then nfa[i]'h' else node := by
  simp at h
  cases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h) with
  | inl lt => simp [lt, pushNode_get_lt _ lt]
  | inr eq => simp [eq]

@[simp, grind =]
theorem pushNode_start_eq {nfa : NFA} {node : Node} : (nfa.pushNode node).start = nfa.nodes.size := rfl

/--
  Compile a Regex and append the resulting nodes to the NFA. The nodes will transition to `next` on match.
-/
def pushRegex (nfa : NFA) (next : Nat) : Expr → NFA
  | .empty => nfa.pushNode .fail
  | .epsilon => nfa.pushNode (.epsilon next)
  | .anchor a => nfa.pushNode (.anchor a next)
  | .char c => nfa.pushNode (.char c next)
  | .classes cs => nfa.pushNode (.sparse cs next)
  | .group index r =>
    -- push the closing save node first
    let nfa' := nfa.pushNode (.save (2 * index + 1) next)
    let nfa'' := nfa'.pushRegex nfa'.start r
    nfa''.pushNode (.save (2 * index) nfa''.start)
  | .alternate r₁ r₂ =>
    -- TODO: it feels better to compile r₂ first to align with concat
    let nfa₁ := nfa.pushRegex next r₁
    let start₁ := nfa₁.start
    let nfa₂ := nfa₁.pushRegex next r₂
    let start₂ := nfa₂.start

    let split := Node.split start₁ start₂

    nfa₂.pushNode split
  | .concat r₁ r₂ =>
    let nfa₂ := nfa.pushRegex next r₂
    nfa₂.pushRegex nfa₂.start r₁
  | .star greedy r =>
    let start := nfa.nodes.size
    -- We need to generate a placeholder node first. We use `fail` for it because
    -- 1. We want to make sure `done` does not appear except at the first node.
    -- 2. variants without data are represented as a boxed integer so there is one less allocation.
    let placeholder := nfa.pushNode .fail
    let compiled := placeholder.pushRegex start r

    let split :=
      if greedy then
        .split compiled.start next
      else
        .split next compiled.start
    -- While we know that `pushRegex` increase the size and hence this `setIfInBounds` is always
    -- in bounds, we don't use that information to eliminate the bounds check. This is because
    -- it requires changing the return type to `{ nfa' : NFA // nfa.nodes.size < nfa'.nodes.size }`
    -- which is much more inconvenient to work with.
    let patched := compiled.nodes.setIfInBounds start split

    ⟨patched, start⟩

def compile (r : Expr) : NFA := done.pushRegex 0 r

end NFA
