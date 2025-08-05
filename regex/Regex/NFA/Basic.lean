import Regex.Data.Anchor
import Regex.Data.Classes
import Lean

set_option autoImplicit false

namespace Regex.NFA

inductive Node where
  | done
  | fail
  | epsilon (next : Nat)
  | anchor (anchor : Regex.Data.Anchor) (next : Nat)
  | char (c : Char) (next : Nat)
  | split (next₁ next₂ : Nat)
  | save (offset : Nat) (next : Nat)
  -- TODO: use an efficient representation
  | sparse (cs : Regex.Data.Classes) (next : Nat)
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

@[inline, always_inline]
def Node.isDone (n : Node) : Bool :=
  match n with
  | .done => true
  | _ => false

def Node.inBounds (n : Node) (size : Nat) : Prop :=
  match n with
  | .done => True
  | .fail => True
  | .epsilon next => next < size
  | .anchor _ next => next < size
  | .char _ next => next < size
  | .split next₁ next₂ => next₁ < size ∧ next₂ < size
  | .save _ next => next < size
  | .sparse _ next => next < size

@[simp]
theorem Node.inBounds.done {size : Nat} : Node.done.inBounds size := by
  simp [inBounds]

@[simp]
theorem Node.inBounds.fail {size : Nat} : Node.fail.inBounds size := by
  simp [inBounds]

@[simp]
theorem Node.inBounds.epsilon {size next : Nat} (h : next < size) :
  (Node.epsilon next).inBounds size := by
  simp [inBounds, h]

@[simp]
theorem Node.inBounds.anchor {size next : Nat} {a : Regex.Data.Anchor} (h : next < size) :
  (Node.anchor a next).inBounds size := by
  simp [inBounds, h]

@[simp]
theorem Node.inBounds.char {size next : Nat} {c : Char} (h : next < size) :
  (Node.char c next).inBounds size := by
  simp [inBounds, h]

@[simp]
theorem Node.inBounds.split {size next₁ next₂ : Nat} (h₁ : next₁ < size) (h₂ : next₂ < size) :
  (Node.split next₁ next₂).inBounds size := by
  simp [inBounds, h₁, h₂]

@[simp]
theorem Node.inBounds.save {size offset next : Nat} (h : next < size) :
  (Node.save offset next).inBounds size := by
  simp [inBounds, h]

theorem Node.lt_of_inBounds.epsilon {size next : Nat} (h : (Node.epsilon next).inBounds size) :
  next < size := by
  simp [inBounds] at h
  exact h

theorem Node.lt_of_inBounds.char {size next : Nat} {c : Char} (h : (Node.char c next).inBounds size) :
  next < size := by
  simp [inBounds] at h
  exact h

theorem Node.lt_of_inBounds.split {size next₁ next₂ : Nat} (h : (Node.split next₁ next₂).inBounds size) :
  next₁ < size ∧ next₂ < size := by
  simp [inBounds] at h
  exact h

theorem Node.lt_of_inBounds.split_left {size next₁ next₂ : Nat} (h : (Node.split next₁ next₂).inBounds size) :
  next₁ < size := (Node.lt_of_inBounds.split h).left

theorem Node.lt_of_inBounds.split_right {size next₁ next₂ : Nat} (h : (Node.split next₁ next₂).inBounds size) :
  next₂ < size := (Node.lt_of_inBounds.split h).right

theorem Node.lt_of_inBounds.save {size offset next : Nat} (h : (Node.save offset next).inBounds size) :
  next < size := by
  simp [inBounds] at h
  exact h

theorem Node.inBounds_of_inBounds_of_le {n : Node} {size size' : Nat} (h : n.inBounds size) (le : size ≤ size') :
  n.inBounds size' := by
  simp [inBounds] at *
  split <;> simp at h <;> try simp
  next => exact Nat.lt_of_lt_of_le h le
  next => exact Nat.lt_of_lt_of_le h le
  next => exact Nat.lt_of_lt_of_le h le
  next => exact ⟨Nat.lt_of_lt_of_le h.left le, Nat.lt_of_lt_of_le h.right le⟩
  next => exact Nat.lt_of_lt_of_le h le
  next => exact Nat.lt_of_lt_of_le h le

instance Node.decInBounds {node : Node} {size : Nat} : Decidable (node.inBounds size) :=
  match node with
  | .done => isTrue trivial
  | .fail => isTrue trivial
  | .epsilon next => inferInstanceAs (Decidable (next < size))
  | .anchor _ next => inferInstanceAs (Decidable (next < size))
  | .char _ next => inferInstanceAs (Decidable (next < size))
  | .sparse _ next => inferInstanceAs (Decidable (next < size))
  | .split next₁ next₂ => inferInstanceAs (Decidable (next₁ < size ∧ next₂ < size))
  | .save _ next => inferInstanceAs (Decidable (next < size))

end Regex.NFA

namespace Regex

/--
  A NFA consists an array of nodes and a designated start node.

  The transition relation and accept nodes are embedded in the nodes themselves.
-/
structure NFA where
  nodes : Array NFA.Node
  start : Nat
deriving Repr, DecidableEq, Inhabited, Lean.ToExpr

instance : ToString NFA where
  toString nfa := reprStr nfa

namespace NFA

def done : NFA :=
  let nodes := #[NFA.Node.done]
  let start := 0
  ⟨nodes, start⟩

def get (nfa : NFA) (i : Nat) (h : i < nfa.nodes.size) : NFA.Node :=
  nfa.nodes[i]

instance : GetElem NFA Nat NFA.Node (fun nfa i => i < nfa.nodes.size) where
  getElem nfa i h := get nfa i h

theorem get_eq_nodes_get (nfa : NFA) (i : Nat) (h : i < nfa.nodes.size) :
  nfa[i] = nfa.nodes[i] := rfl

def maxTag (nfa : NFA) : Nat :=
  nfa.nodes.foldl (init := 0) fun accum node =>
    match node with
    | .save tag _ => accum.max tag
    | _ => accum

theorem le_maxTag {tag next} (nfa : NFA) (i : Fin nfa.nodes.size) (eq : nfa[i] = .save tag next) :
  tag ≤ nfa.maxTag := by
  unfold maxTag
  let motive (i : Nat) (maxTag : Nat) : Prop :=
    ∀ j next (lt₁ : j < i) (lt₂ : j < nfa.nodes.size) (eq : nfa[j] = .save tag next), tag ≤ maxTag
  refine Array.foldl_induction motive
    ?h0 ?hf i.val next i.isLt i.isLt eq
  case h0 => simp [motive]
  case hf =>
    intro i maxTag accum
    simp [motive]
    intro j next lt₁ lt₂ eq
    split
    next tag' next' heq =>
      cases Nat.lt_succ_iff_lt_or_eq.mp lt₁ with
      | inl lt =>
        have := accum j next lt lt₂ eq
        exact Nat.le_trans this (Nat.le_max_left ..)
      | inr eq' =>
        simp [eq', get_eq_nodes_get] at eq
        simp [eq] at heq
        exact heq.1 ▸ Nat.le_max_right ..
    next ne =>
      cases Nat.lt_succ_iff_lt_or_eq.mp lt₁ with
      | inl lt => exact accum j next lt lt₂ eq
      | inr eq' =>
        simp [eq', get_eq_nodes_get] at eq
        exact absurd eq (ne tag next)

structure WellFormed (nfa : NFA) : Prop where
  start_lt : nfa.start < nfa.nodes.size
  inBounds : ∀ i : Fin nfa.nodes.size, nfa[i].inBounds nfa.nodes.size

theorem WellFormed.iff {nfa : NFA} :
  nfa.WellFormed ↔ nfa.start < nfa.nodes.size ∧ ∀ i : Fin nfa.nodes.size, nfa[i].inBounds nfa.nodes.size :=
  ⟨fun wf => ⟨wf.start_lt, wf.inBounds⟩, fun ⟨h₁, h₂⟩ => ⟨h₁, h₂⟩⟩

theorem WellFormed.inBounds' {nfa : NFA} {node : NFA.Node} (wf : nfa.WellFormed) (i : Fin nfa.nodes.size) (hn : nfa[i] = node) :
  node.inBounds nfa.nodes.size := by
  rw [←hn]
  exact wf.inBounds i

theorem done_WellFormed : done.WellFormed :=
  have start_lt : 0 < done.nodes.size := by
    simp [done]
  have inBounds (i : Fin done.nodes.size) : done[i].inBounds done.nodes.size := by
    match i with
    | ⟨0, isLt⟩ =>
      simp [done, Node.inBounds]
      split <;> try contradiction
      trivial
    | ⟨_ + 1, isLt⟩ => contradiction
  ⟨start_lt, inBounds⟩

instance decWellFormed (nfa : NFA) : Decidable nfa.WellFormed :=
  let decStartLt := inferInstanceAs (Decidable (nfa.start < nfa.nodes.size))
  match decStartLt with
  | isTrue h₁ =>
    let decInBounds := inferInstanceAs (Decidable (∀ i : Fin nfa.nodes.size, nfa[i].inBounds nfa.nodes.size))
    match decInBounds with
    | isTrue h₂ => isTrue ⟨h₁, h₂⟩
    | isFalse h₂ => isFalse (fun h => absurd h.2 h₂)
  | isFalse h₁ => isFalse (fun h => absurd h.1 h₁)

end NFA
end Regex
