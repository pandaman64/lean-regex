import Regex.Data.Expr
import Regex.NFA.Basic

import Batteries.Data.Array.Lemmas

open Regex.Data (Expr)

namespace Regex.NFA

def pushNode (nfa : NFA) (node : Node) (inBounds : node.inBounds (nfa.nodes.size + 1)) :
  { nfa' : NFA // nfa.nodes.size < nfa'.nodes.size } :=
  let start := nfa.nodes.size
  let nodes := nfa.nodes.push node
  have inBounds := by
    intro i
    simp [nodes]
    rw [Array.get_push]
    split
    case isTrue h =>
      have := nfa.inBounds ⟨i.val, h⟩
      apply Node.inBounds_of_inBounds_of_le this (Nat.le_succ _)
    case isFalse => exact inBounds
  let nfa' : NFA := ⟨nodes, ⟨start, by simp [nodes]⟩, inBounds⟩

  ⟨nfa', by simp [nodes]⟩

@[simp]
theorem pushNode_size {nfa : NFA} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)} :
  (nfa.pushNode node inBounds).val.nodes.size = nfa.nodes.size + 1 := by
  simp [pushNode]

theorem pushNode_get_lt {nfa : NFA} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)}
  (i : Nat) (h : i < nfa.nodes.size) :
  (nfa.pushNode node inBounds).val[i]'(Nat.lt_trans h (nfa.pushNode node inBounds).property) = nfa[i] := by
  simp [pushNode, get_eq_nodes_get]
  rw [Array.get_push_lt]

@[simp]
theorem pushNode_get_eq {nfa : NFA} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)} :
  (nfa.pushNode node inBounds).val[nfa.nodes.size] = node := by
  simp [pushNode, get_eq_nodes_get]

theorem pushNode_get {nfa : NFA} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)}
  (i : Nat) (h : i < (nfa.pushNode node inBounds).val.nodes.size) :
  (nfa.pushNode node inBounds).val[i]'h = if h' : i < nfa.nodes.size then nfa[i]'h' else node := by
  simp at h
  cases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h) with
  | inl lt => simp [lt, pushNode_get_lt _ lt]
  | inr eq => simp [eq]

@[simp]
theorem pushNode_start_eq {nfa : NFA} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)} :
  (nfa.pushNode node inBounds).val.start.val = nfa.nodes.size := rfl

/--
  Compile a Regex and append the resulting nodes to the NFA. The nodes will transition to `next` on match.
-/
def pushRegex (nfa : NFA) (next : Fin nfa.nodes.size) :
  Expr → { nfa' : NFA // nfa.nodes.size < nfa'.nodes.size }
  | .empty => nfa.pushNode .fail (by simp)
  | .epsilon => nfa.pushNode (.epsilon next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))
  | .char c => nfa.pushNode (.char c next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))
  | .classes c => nfa.pushNode (.sparse c next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))
  | .group index r =>
    -- push the closing save node first
    let nfa' := nfa.pushNode (.save (2 * index + 1) next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))
    let nfa'' := nfa'.val.pushRegex nfa'.val.start r
    let nfa''' := nfa''.val.pushNode (.save (2 * index) nfa''.val.start) (by simp [Node.inBounds]; exact Nat.lt_trans nfa''.val.start.isLt (Nat.lt_succ_self _))

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
    let nfa₂ := nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ r₂
    let start₂ := nfa₂.val.start

    let split := Node.split start₁ start₂
    have inBounds : split.inBounds (nfa₂.val.nodes.size + 1) := by
      have lt₁ : start₁ < nfa₂.val.nodes.size + 1 :=
        calc
          _ < _ := start₁.isLt
          _ < _ := nfa₂.property
          _ < _ := Nat.lt_succ_self _
      have lt₂ : start₂ < nfa₂.val.nodes.size + 1 := Nat.lt_trans start₂.isLt (Nat.lt_succ_self _)
      simp [split, lt₁, lt₂]

    let nfa' := nfa₂.val.pushNode split inBounds
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
    -- 1. We'll use the fact that `fail` is a minimal element when strengthening induction hypotheis;
    -- 2. We want to make sure `done` does not appear except at the first node.
    -- 3. variants without data are represented as a boxed integer so there is one less allocation.
    let placeholder := nfa.pushNode .fail (by simp)
    let loopStart := placeholder.val.start
    -- FIXME: generated code keeps `placeholder` alive, copying the array. Why?
    let compiled := placeholder.val.pushRegex loopStart r

    -- Patch the placeholder node
    have isLt : loopStart.val < compiled.val.nodes.size :=
      calc
        _ < _ := loopStart.isLt
        _ < _ := compiled.property
    let loopStart := ⟨loopStart.val, isLt⟩

    let split := Node.split compiled.val.start next
    let patched := compiled.val.nodes.set loopStart split
    have inBounds : ∀ i : Fin patched.size, patched[i].inBounds patched.size := by
      simp [patched]
      intro i
      have hj : i < compiled.val.nodes.size := by
        suffices i.val < (compiled.val.nodes.set loopStart split).size by
          simp at this
          exact this
        exact i.isLt
      rw [Array.get_set (hj := hj)]
      split
      case isTrue =>
        have lt₁ : compiled.val.start < compiled.val.nodes.size := compiled.val.start.isLt
        have lt₂ : next < compiled.val.nodes.size :=
          calc
            _ < _ := next.isLt
            _ < _ := placeholder.property
            _ < _ := compiled.property
        simp [compiled, split, lt₁, lt₂]
      case isFalse neq =>
        have := compiled.val.inBounds ⟨i, hj⟩
        simp at this
        exact this

    let nfa' := ⟨patched, loopStart.cast (by rw [Array.size_set]), inBounds⟩
    have property :=
      calc
        _ < _ := placeholder.property
        _ < _ := compiled.property
        _ = nfa'.nodes.size := by simp [patched]

    ⟨nfa', property⟩

@[export lean_regex_compile]
def compile (r : Expr) : NFA := done.pushRegex ⟨0, by decide⟩ r

-- Useful lemmas about the compilation
def pushRegex.empty (eq : pushRegex nfa next .empty = result)
  {motive : result = nfa.pushNode .fail (by simp) → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

def pushRegex.epsilon (eq : pushRegex nfa next .epsilon = result)
  {motive : result = nfa.pushNode (.epsilon next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _)) → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

def pushRegex.char (eq : pushRegex nfa next (.char c) = result)
  {motive : result = nfa.pushNode (.char c next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _)) → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

def pushRegex.sparse
  (eq : pushRegex nfa next (.classes c) = result)
  {motive : result = nfa.pushNode (.sparse c next)
  ((by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))) → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

def pushRegex.group (eq : pushRegex nfa next (.group index r) = result)
  {motive : ∀ nfa' nfa'' nfa''' property inBounds' inBounds''',
    nfa' = nfa.pushNode (.save (2 * index + 1) next) inBounds' →
    nfa'' = nfa'.val.pushRegex nfa'.val.start r →
    nfa''' = nfa''.val.pushNode (.save (2 * index) nfa''.val.start) inBounds''' →
    result = ⟨nfa''', property⟩ →
    P
  } : P := by
  have inBounds' : (Node.save (2 * index + 1) next).inBounds (Array.size nfa.nodes + 1) := by
    simp [Node.inBounds]
    exact Nat.lt_trans next.isLt (Nat.lt_succ_self _)
  let nfa' := nfa.pushNode (.save (2 * index + 1) next) inBounds'
  let nfa'' := nfa'.val.pushRegex nfa'.val.start r
  have inBounds''' : (Node.save (2 * index) nfa''.val.start).inBounds (Array.size nfa''.val.nodes + 1) := by
    simp [Node.inBounds]
    exact Nat.lt_trans nfa''.val.start.isLt (Nat.lt_succ_self _)
  let nfa''' := nfa''.val.pushNode (.save (2 * index) nfa''.val.start) inBounds'''

  have property : nfa.nodes.size < nfa'''.val.nodes.size :=
    calc
      _ < _ := nfa'.property
      _ < _ := nfa''.property
      _ < _ := nfa'''.property

  exact motive nfa' nfa'' nfa''' property inBounds' inBounds''' rfl rfl rfl eq.symm

def pushRegex.alternate (eq : pushRegex nfa next (.alternate r₁ r₂) = result)
  {motive : ∀ nfa₁ start₁ nfa₂ start₂ inBounds nfa' property,
    nfa₁ = nfa.pushRegex next r₁ →
    start₁ = nfa₁.val.start →
    nfa₂ = nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ r₂ →
    start₂ = nfa₂.val.start →
    nfa' = nfa₂.val.pushNode (.split start₁ start₂) inBounds →
    result = ⟨nfa', property⟩ →
    P
  } : P := by
  let nfa₁ := nfa.pushRegex next r₁
  let start₁ := nfa₁.val.start
  let nfa₂ := nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ r₂
  let start₂ := nfa₂.val.start

  let split := Node.split start₁ start₂
  have inBounds : split.inBounds (nfa₂.val.nodes.size + 1) := by
    have lt₁ : start₁ < nfa₂.val.nodes.size + 1 :=
      calc
        _ < _ := start₁.isLt
        _ < _ := nfa₂.property
        _ < _ := Nat.lt_succ_self _
    have lt₂ : start₂ < nfa₂.val.nodes.size + 1 := Nat.lt_trans start₂.isLt (Nat.lt_succ_self _)
    simp [split, lt₁, lt₂]

  let nfa' := nfa₂.val.pushNode split inBounds
  have property : nfa.nodes.size < nfa'.val.nodes.size :=
    calc
      _ < _ := nfa₁.property
      _ < _ := nfa₂.property
      _ < _ := nfa'.property

  exact motive nfa₁ start₁ nfa₂ start₂ inBounds nfa' property rfl rfl rfl rfl rfl eq.symm

def pushRegex.concat (eq : pushRegex nfa next (.concat r₁ r₂) = result)
  {motive : ∀ nfa₂ nfa₁ property,
    nfa₂ = nfa.pushRegex next r₂ →
    nfa₁ = nfa₂.val.pushRegex nfa₂.val.start r₁ →
    result = ⟨nfa₁, property⟩ →
    P
  } : P := by
  let nfa₂ := nfa.pushRegex next r₂
  let nfa₁ := nfa₂.val.pushRegex nfa₂.val.start r₁

  have property : nfa.nodes.size < nfa₁.val.nodes.size :=
    calc
      _ < _ := nfa₂.property
      _ < _ := nfa₁.property

  exact motive nfa₂ nfa₁ property rfl rfl eq.symm

def pushRegex.star (eq : pushRegex nfa next (.star r) = result)
  {motive : ∀ placeholder compiled patched nfa' isLt inBounds property,
    placeholder = nfa.pushNode .fail (by simp) →
    compiled = placeholder.val.pushRegex ⟨nfa.nodes.size, placeholder.property⟩ r →
    patched = compiled.val.nodes.set
      ⟨nfa.nodes.size, Nat.lt_trans placeholder.property compiled.property⟩
      (Node.split compiled.val.start next) →
    nfa' = ⟨patched, ⟨nfa.nodes.size, isLt⟩, inBounds⟩ →
    result = ⟨nfa', property⟩ →
    P
  } : P := by
  let placeholder := nfa.pushNode .fail (by simp)
  let compiled := placeholder.val.pushRegex ⟨nfa.nodes.size, placeholder.property⟩ r

  -- Patch the placeholder node
  let loopStart : Fin _ := ⟨nfa.nodes.size, Nat.lt_trans placeholder.property compiled.property⟩
  let split := Node.split compiled.val.start next
  let patched := compiled.val.nodes.set loopStart split
  have inBounds : ∀ i : Fin patched.size, patched[i].inBounds patched.size := by
    simp [patched]
    intro i
    have hj : i < compiled.val.nodes.size := by
      suffices i.val < (compiled.val.nodes.set loopStart split).size by
        simp at this
        exact this
      exact i.isLt
    rw [Array.get_set (hj := hj)]
    split
    case isTrue =>
      have lt₁ : compiled.val.start < compiled.val.nodes.size := compiled.val.start.isLt
      have lt₂ : next < compiled.val.nodes.size :=
        calc
          _ < _ := next.isLt
          _ < _ := placeholder.property
          _ < _ := compiled.property
      simp [split, lt₁, lt₂]
    case isFalse neq =>
      have := compiled.val.inBounds ⟨i, hj⟩
      simp at this
      exact this

  have isLt : nfa.nodes.size < patched.size :=
    calc
      _ < _ := placeholder.property
      _ < _ := compiled.property
      _ = _ := by simp [patched]
  let nfa' : NFA := ⟨patched, ⟨nfa.nodes.size, isLt⟩, inBounds⟩
  have property :=
    calc
      _ < _ := placeholder.property
      _ < _ := compiled.property
      _ = nfa'.nodes.size := by simp [patched]

  exact motive placeholder compiled patched nfa' isLt inBounds property rfl rfl rfl rfl eq.symm

end NFA
