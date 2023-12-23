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

/--
  The NFA consists an array of nodes and a designated start node.

  The transition relation and accept nodes are embedded in the nodes themselves.
-/
structure NFA where
  nodes : Array Node
  start : Fin nodes.size
deriving Repr

def NFA.get (nfa : NFA) (i : Nat) (h : i < nfa.nodes.size) : Node :=
  nfa.nodes[i]

instance : GetElem NFA Nat Node (fun nfa i => i < nfa.nodes.size) where
  getElem := NFA.get

theorem NFA.eq_get {nfa : NFA} {i : Nat} {h : i < nfa.nodes.size} :
  nfa[i] = nfa.nodes[i] := rfl

end NFA
