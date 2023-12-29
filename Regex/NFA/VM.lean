import Regex.NFA.Basic

-- TODO: use a bitvec?
abbrev NodeSet (n : Nat) := { array : Array Bool // array.size = n }

def NodeSet.get (ns : NodeSet n) (i : Fin n) : Bool :=
  ns.val.get (ns.property.symm ▸ i)

def NodeSet.set (ns : NodeSet n) (i : Fin n) : NodeSet n :=
  ⟨ns.val.set (ns.property.symm ▸ i) true, by simp [ns.property]⟩

def NodeSet.unset (ns : NodeSet n) (i : Fin n) : NodeSet n :=
  ⟨ns.val.set (ns.property.symm ▸ i) false, by simp [ns.property]⟩

def NodeSet.size (ns : NodeSet n) : Nat :=
  go ns 0 0 (Nat.zero_le _)
where
  go (ns : NodeSet n) (accum : Nat) (i : Nat) (hle : i ≤ n) : Nat :=
    if h : i = n then
      accum
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      let accum := if ns.get ⟨i, hlt⟩ then accum + 1 else accum
      go ns accum (i + 1) hlt
termination_by go _ => n - i

def NodeSet.clear (ns : NodeSet n) : NodeSet n :=
  go ns 0 (Nat.zero_le _)
where
  go (ns : NodeSet n) (i : Nat) (hle : i ≤ n) : NodeSet n :=
    if h : i = n then
      ns
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      go (ns.unset ⟨i, hlt⟩) (i + 1) hlt
termination_by go _ => n - i

def NodeSet.empty {n : Nat} : NodeSet n :=
  ⟨mkArray n false, by simp⟩

open NFA

structure NodeSets (n : Nat) where
  visited : NodeSet n
  current : NodeSet n
deriving Repr

instance : ToString (NodeSets n) where
  toString ns := reprStr ns

def NodeSets.init (current : NodeSet n) : NodeSets n :=
  ⟨NodeSet.empty, current⟩

partial def addεClosure (nfa : NFA) (i : Nat) (sets : NodeSets nfa.nodes.size) : NodeSets nfa.nodes.size :=
  if hlt : i < nfa.nodes.size then
    let ⟨visited, ns⟩ := sets
    if visited.get ⟨i, hlt⟩ then
      sets
    else
      let visited := visited.set ⟨i, hlt⟩
      let ns := ns.set ⟨i, hlt⟩
      match nfa[i] with
      | .epsilon next => addεClosure nfa next ⟨visited, ns⟩
      | .split next₁ next₂ => addεClosure nfa next₂ (addεClosure nfa next₁ ⟨visited, ns⟩)
      | _ => ⟨visited, ns⟩
  else
    sets

-- TODO: reuse allocation
def charStep (nfa : NFA) (c : Char) (init : NodeSet nfa.nodes.size) :
  NodeSet nfa.nodes.size := go nfa (NodeSets.init NodeSet.empty) init c 0 (Nat.zero_le _)
where
  go (nfa : NFA) (accum : NodeSets nfa.nodes.size) (init : NodeSet nfa.nodes.size) (c : Char)
    (i : Nat) (hle : i ≤ nfa.nodes.size) : NodeSet nfa.nodes.size :=
    if h : i = nfa.nodes.size then
      accum.current
    else
      have hlt : i < nfa.nodes.size := Nat.lt_of_le_of_ne hle h
      let accum := if init.get ⟨i, hlt⟩ then
        match nfa[i] with
        | .char c' next => if c = c' then addεClosure nfa next accum else accum
        | _ => accum
      else accum
      go nfa accum init c (i + 1) hlt
termination_by go _ => nfa.nodes.size - i

partial def NFA.NFA.run (nfa : NFA) (s : String) : Bool :=
  if h : 0 < nfa.nodes.size then
    let ns := addεClosure (dbgTraceVal nfa) nfa.start (NodeSets.init NodeSet.empty)
    let ns := go nfa s 0 ns.current
    -- This assumes that the first node is the accepting node
    ns.get ⟨0, h⟩
  else
    false
where
  go (nfa : NFA) (s : String) (i : String.Pos) (ns : NodeSet nfa.nodes.size) : NodeSet nfa.nodes.size :=
    if s.atEnd i then
      ns
    else
      let c := s.get i
      let ns' := charStep nfa c ns
      dbgTrace s!"{ns} ⟶{c} {ns'}" (fun () => go nfa s (s.next i) ns')
