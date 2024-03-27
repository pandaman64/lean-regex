import Regex.NFA.Basic

import Mathlib.Data.Set.Basic

namespace NFA

/- Returns the set of nodes that can be reached from the given node by consuming the given character. -/
def Node.charStep (n : Node) (c : Char) : Set Nat :=
  match n with
  | Node.char c' next => if c == c' then {next} else ∅
  | Node.sparse ranges next => if ranges.in c then {next} else ∅
  | _ => ∅

/- Returns the set of nodes that can be reached from the given node by consuming ε. -/
def Node.εStep (n : Node) : Set Nat :=
  match n with
  | Node.epsilon next => {next}
  | Node.split next₁ next₂ => {next₁, next₂}
  | Node.save _ next => {next}
  | _ => ∅

/- Returns the set of nodes that can be reached from the given node by consuming the given character. -/
def charStep (nfa : NFA) (i : Nat) (c : Char) : Set Nat :=
  if h : i < nfa.nodes.size
    then nfa[i].charStep c
    else ∅

/- Returns the set of nodes that can be reached from the given node by consuming ε. -/
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
  split at mem <;> try simp [Node.inBounds] at *
  simp [*]
  cases mem ; simp [*]

theorem lt_of_inBounds_of_εStep {node : Node} {j k : Nat}
  (inBounds : node.inBounds k) (mem : j ∈ node.εStep) :
  j < k := by
  unfold Node.εStep at mem
  split at mem <;>
    try simp [Node.inBounds] at * <;>
    try cases mem <;>
    simp [*]

theorem lt_of_εStep {nfa : NFA} {i j : Nat} {h : i < nfa.nodes.size}
  (mem : j ∈ nfa[i].εStep) : j < nfa.nodes.size := by
  have inBounds := nfa.inBounds ⟨i, h⟩
  simp [get_eq_nodes_get] at mem
  exact lt_of_inBounds_of_εStep inBounds mem

theorem lt_of_charStep {nfa : NFA} {i j : Nat} {h : i < nfa.nodes.size}
  (mem : j ∈ nfa[i].charStep c) : j < nfa.nodes.size := by
  have inBounds := nfa.inBounds ⟨i, h⟩
  simp [get_eq_nodes_get] at mem
  exact lt_of_inBounds_of_charStep inBounds mem

-- def step (nfa : NFA) (i : Fin nfa.nodes.size) (c : Option Char) : Set (Fin nfa.nodes.size) :=
--   match c, nfa[i], nfa.inBounds i with
--   | .some c, .char c' next, inBounds =>
--     if c == c' then {⟨next, Node.lt_of_inBounds.char inBounds⟩} else ∅
--   | .none, .epsilon next, inBounds => {⟨next, Node.lt_of_inBounds.epsilon inBounds⟩}
--   | .none, .split next₁ next₂, inBounds =>
--     have lt := Node.lt_of_inBounds.split inBounds
--     {⟨next₁, lt.left⟩, ⟨next₂, lt.right⟩}
--   | _, _, _ => ∅

-- theorem charStep_cases {nfa : NFA} {i j : Fin nfa.nodes.size} {c : Char}
--   (h : j ∈ nfa.step i (.some c)) (char : nfa[i.val] = Node.char c j.val → motive)
--   : motive := by
--   simp [step] at h
--   split at h <;> try simp [*] at *
--   next c' c'' next _ eqn eqc _ =>
--     apply char
--     simp [eqn, eqc, h]

-- theorem εStep_cases {nfa : NFA} {i j : Fin nfa.nodes.size}
--   (h : j ∈ nfa.step i .none)
--   (epsilon : nfa[i.val] = Node.epsilon j.val → motive)
--   (split : ∀ next₁ next₂, nfa[i.val] = Node.split next₁ next₂ → j.val = next₁ ∨ j.val = next₂ → motive) :
--   motive := by
--   simp [step] at h
--   split at h <;> try simp [*] at *
--   next next _ eqn _ _ =>
--     apply epsilon
--     simp [eqn, h]
--   next next₁ next₂ _ eqn _ _ =>
--     apply split next₁ next₂ eqn
--     cases h <;> simp [*]

-- theorem step_cases {nfa : NFA} {i j : Fin nfa.nodes.size} (h : j ∈ nfa.step i c)
--   (char : ∀ c', c = .some c' → nfa[i.val] = Node.char c' j.val → motive)
--   (epsilon : c = none → nfa[i.val] = Node.epsilon j.val → motive)
--   (split : ∀ next₁ next₂, c = none → nfa[i.val] = Node.split next₁ next₂ →
--     j.val = next₁ ∨ j.val = next₂ → motive) :
--   motive := by
--   cases c with
--   | none => apply εStep_cases h (epsilon rfl) (fun next₁ next₂ => split _ _ rfl)
--   | some c' => apply charStep_cases h (char c' rfl)

end NFA
