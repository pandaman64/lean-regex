import Regex.NFA.Basic

import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Insert

namespace Regex.NFA

def Node.charStep (n : Node) (c : Char) : Set Nat :=
  match n with
  | Node.char c' next => if c == c' then {next} else ∅
  | Node.sparse cs next => if c ∈ cs then {next} else ∅
  | _ => ∅

def Node.εStep (n : Node) : Set Nat :=
  match n with
  | Node.epsilon next => {next}
  | Node.split next₁ next₂ => {next₁, next₂}
  | Node.save _ next => {next}
  | _ => ∅

def charStep (nfa : NFA) (i : Nat) (c : Char) : Set Nat :=
  if h : i < nfa.nodes.size
    then nfa[i].charStep c
    else ∅

def εStep (nfa : NFA) (i : Nat) : Set Nat :=
  if h : i < nfa.nodes.size
    then nfa[i].εStep
    else ∅

theorem charStep_of_charStep {nfa : NFA} {i : Nat} {c : Char} {h : i < nfa.nodes.size}
  (mem : j ∈ nfa[i].charStep c) :
  j ∈ nfa.charStep i c := by
  simp [charStep, h, mem]

theorem εStep_of_εStep {nfa : NFA} {i : Nat} {h : i < nfa.nodes.size}
  (mem : j ∈ nfa[i].εStep) :
  j ∈ nfa.εStep i := by
  simp [εStep, h, mem]

theorem lt_of_inBounds_of_charStep {node : Node} {j k : Nat} {c : Char}
  (inBounds : node.inBounds k) (mem : j ∈ node.charStep c) :
  j < k := by
  unfold Node.charStep at mem
  split at mem <;> try simp_all [Node.inBounds]

theorem lt_of_inBounds_of_εStep {node : Node} {j k : Nat}
  (inBounds : node.inBounds k) (mem : j ∈ node.εStep) :
  j < k := by
  unfold Node.εStep at mem
  split at mem <;>
    try simp_all [Node.inBounds] <;>
    try cases mem <;>
    simp_all

theorem lt_of_εStep {nfa : NFA} {i j : Nat} {h : i < nfa.nodes.size}
  (wf : nfa.WellFormed) (mem : j ∈ nfa[i].εStep) : j < nfa.nodes.size := by
  have inBounds := wf.inBounds ⟨i, h⟩
  simp [get_eq_nodes_get] at mem
  exact lt_of_inBounds_of_εStep inBounds mem

theorem lt_of_charStep {nfa : NFA} {i j : Nat} {h : i < nfa.nodes.size}
  (wf : nfa.WellFormed) (mem : j ∈ nfa[i].charStep c) : j < nfa.nodes.size := by
  have inBounds := wf.inBounds ⟨i, h⟩
  simp [get_eq_nodes_get] at mem
  exact lt_of_inBounds_of_charStep inBounds mem

end Regex.NFA
