import Mathlib.Data.Set.Basic

namespace NFA

inductive Node where
  | done
  | fail
  | epsilon (next : Nat)
  | char (c : Char) (next : Nat)
  | split (next₁ next₂ : Nat)
deriving Repr

def Node.charStep (n : Node) (c : Char) : Set Nat :=
  match n with
  | Node.char c' next => if c == c' then {next} else ∅
  | _ => ∅

def Node.εStep (n : Node) : Set Nat :=
  match n with
  | Node.epsilon next => {next}
  | Node.split next₁ next₂ => {next₁, next₂}
  | _ => ∅

def Node.inBounds (n : Node) (size : Nat) : Prop :=
  (∀ c, n.charStep c ⊆ { j | j < size }) ∧ n.εStep ⊆ { j | j < size }

@[simp]
theorem Node.inBounds.done {size : Nat} : Node.done.inBounds size := by
  simp [inBounds, charStep, εStep]

@[simp]
theorem Node.inBounds.fail {size : Nat} : Node.fail.inBounds size := by
  simp [inBounds, charStep, εStep]

@[simp]
theorem Node.inBounds.epsilon {size next : Nat} (h : next < size) :
  (Node.epsilon next).inBounds size := by
  simp [inBounds, charStep, εStep, h]

@[simp]
theorem Node.inBounds.char {size next : Nat} {c : Char} (h : next < size) :
  (Node.char c next).inBounds size := by
  simp [inBounds, charStep, εStep]
  intro c'
  split <;> simp [h]

@[simp]
theorem Node.inBounds.split {size next₁ next₂ : Nat} (h₁ : next₁ < size) (h₂ : next₂ < size) :
  (Node.split next₁ next₂).inBounds size := by
  simp [inBounds, charStep, εStep]
  apply Set.insert_subset <;> simp [h₁, h₂]

theorem Node.inBounds_of_inBounds_of_le {n : Node} (h : n.inBounds size) (le : size ≤ size') :
  n.inBounds size' := by
  simp [inBounds] at *
  apply And.intro
  . intro c
    apply le_trans (h.left c)
    simp
    intro j h
    exact Nat.lt_of_lt_of_le h le
  . apply le_trans h.right
    simp
    intro j h
    exact Nat.lt_of_lt_of_le h le

/--
  The NFA consists an array of nodes and a designated start node.

  The transition relation and accept nodes are embedded in the nodes themselves.
-/
structure NFA where
  nodes : Array Node
  start : Fin nodes.size
deriving Repr

instance : ToString NFA where
  toString nfa := reprStr nfa

def NFA.get (nfa : NFA) (i : Nat) (h : i < nfa.nodes.size) : Node :=
  nfa.nodes[i]

instance : GetElem NFA Nat Node (fun nfa i => i < nfa.nodes.size) where
  getElem := NFA.get

theorem NFA.eq_get {nfa : NFA} {i : Nat} {h : i < nfa.nodes.size} :
  nfa[i] = nfa.nodes[i] := rfl

def NFA.inBounds (nfa : NFA) :=
  ∀ i : Fin nfa.nodes.size, nfa[i].inBounds nfa.nodes.size

theorem NFA.zero_lt_size {nfa : NFA} : 0 < nfa.nodes.size := by
  apply Nat.zero_lt_of_ne_zero
  intro h
  exact (h ▸ nfa.start).elim0

end NFA
