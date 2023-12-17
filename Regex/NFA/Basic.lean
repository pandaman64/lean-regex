import Mathlib.Computability.EpsilonNFA

namespace NFA

inductive Node where
  | done
  | fail
  | epsilon (next : Nat)
  | char (c : Char) (next : Nat)
  | split (next₁ next₂ : Nat)
deriving Repr

def Node.inBounds (n : Node) (nodes : Array Node) : Bool :=
  match n with
  | Node.done | Node.fail => true
  | Node.epsilon next | Node.char _ next => next < nodes.size
  | Node.split next₁ next₂ => next₁ < nodes.size && next₂ < nodes.size

theorem Node.inBounds.epsilon (h : inBounds (.epsilon next) nodes) : next < nodes.size := by
  simp [inBounds] at h
  assumption

theorem Node.inBounds.char (h : inBounds (.char c next) nodes) : next < nodes.size := by
  simp [inBounds] at h
  assumption

theorem Node.inBounds.splitL (h : inBounds (.split next₁ next₂) nodes) : next₁ < nodes.size := by
  simp [inBounds] at h
  exact h.left

theorem Node.inBounds.splitR (h : inBounds (.split next₁ next₂) nodes) : next₂ < nodes.size := by
  simp [inBounds] at h
  exact h.right

structure NFA where
  nodes : Array Node
  start : Fin nodes.size
  inBounds : ∀ id : Fin nodes.size, nodes[id].inBounds nodes
deriving Repr

abbrev NodeId (nfa : NFA) := Fin nfa.nodes.size

abbrev SafeNode (nfa : NFA) := { n : Node // n.inBounds nfa.nodes }

def NFA.get (nfa : NFA) (id : NodeId nfa) : SafeNode nfa :=
  ⟨nfa.nodes[id], nfa.inBounds id⟩

def NFA.step (nfa : NFA) (id : NodeId nfa) (c : Option Char) : Set (NodeId nfa) :=
  match nfa.get id, c with
  | ⟨.char c' next, prop⟩, some c => if c = c' then {⟨next, Node.inBounds.char prop⟩} else ∅
  | ⟨.epsilon next, prop⟩, none => {⟨next, Node.inBounds.epsilon prop⟩}
  | ⟨.split next₁ next₂, prop⟩, none =>
    {⟨next₁, Node.inBounds.splitL prop⟩, ⟨next₂, Node.inBounds.splitR prop⟩}
  | _, _ => ∅

def NFA.accept (nfa : NFA) : Set (NodeId nfa) := { id : NodeId nfa | (nfa.get id).val = .done }

def NFA.toMathlibεNFA (nfa : NFA) : εNFA Char (NodeId nfa) :=
  ⟨nfa.step, {nfa.start}, nfa.accept⟩

def NFA.accepts (nfa : NFA) (cs : List Char) :=
  (nfa.toMathlibεNFA).accepts cs

end NFA
