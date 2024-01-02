import Regex.Lemmas
import Regex.NFA.Basic

-- TODO: use a bitvec?
abbrev NodeSet (n : Nat) := { array : Array Bool // array.size = n }

def NodeSet.empty {n : Nat} : NodeSet n :=
  ⟨mkArray n false, by simp⟩

def NodeSet.get (ns : NodeSet n) (i : Fin n) : Bool :=
  ns.val.get (i.cast ns.property.symm)

def NodeSet.set (ns : NodeSet n) (i : Fin n) : NodeSet n :=
  ⟨ns.val.set (i.cast ns.property.symm) true, by simp [ns.property]⟩

@[simp]
theorem NodeSet.get_set_eq (ns : NodeSet n) (i : Fin n) :
  (ns.set i).get i = true := by
  simp [NodeSet.get, NodeSet.set]
  rw [Array.get_set]
  . simp
  . simp [ns.property]

theorem NodeSet.get_set_ne (ns : NodeSet n) (i j : Fin n) (ne : i.val ≠ j.val) :
  (ns.set i).get j = ns.get j := by
  simp [NodeSet.get, NodeSet.set]
  rw [Array.get_set]
  . simp [ne]
  . simp [ns.property, ne]

def NodeSet.unset (ns : NodeSet n) (i : Fin n) : NodeSet n :=
  ⟨ns.val.set (i.cast  ns.property.symm) false, by simp [ns.property]⟩

@[simp]
theorem NodeSet.get_unset_eq (ns : NodeSet n) (i : Fin n) :
  (ns.unset i).get i = false := by
  simp [NodeSet.get, NodeSet.unset]
  rw [Array.get_set]
  . simp
  . simp [ns.property]

theorem NodeSet.get_unset_ne (ns : NodeSet n) (i j : Fin n) (ne : i.val ≠ j.val) :
  (ns.unset i).get j = ns.get j := by
  simp [NodeSet.get, NodeSet.unset]
  rw [Array.get_set]
  . simp [ne]
  . simp [ns.property, ne]

def NodeSet.count_set (ns : NodeSet n) : Nat :=
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

def NodeSet.count_unset (ns : NodeSet n) : Nat :=
  go ns 0 0 (Nat.zero_le _)
where
  go (ns : NodeSet n) (accum : Nat) (i : Nat) (hle : i ≤ n) : Nat :=
    if h : i = n then
      accum
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      let accum := if ns.get ⟨i, hlt⟩ then accum else accum + 1
      go ns accum (i + 1) hlt
termination_by go _ => n - i

theorem NodeSet.lt_count_unset (ns : NodeSet n) (lt : x < n) (unset : ¬ ns.get ⟨x, lt⟩) :
  (ns.set ⟨x, lt⟩).count_unset < ns.count_unset := by
  let inv (i accum₁ accum₂ : Nat) : Prop :=
    if i > x then
      accum₁ + 1 = accum₂
    else
      accum₁ = accum₂

  let rec go {i accum₁ accum₂ : Nat} (inv₀ : inv i accum₁ accum₂) (hle : i ≤ n) :
    count_unset.go (ns.set ⟨x, lt⟩) accum₁ i hle + 1 = count_unset.go ns accum₂ i hle := by
    simp [inv, lt] at *
    split at inv₀
    case inl lt' =>
      unfold count_unset.go
      cases Nat.decEq i n with
      | isTrue eq =>
        simp [eq]
        exact inv₀
      | isFalse neq =>
        simp [neq]
        have hlt : i < n := Nat.lt_of_le_of_ne hle neq
        rw [NodeSet.get_set_ne]
        . have lt'' : x < i + 1 := Nat.lt_trans lt' (Nat.lt_succ_self _)
          have invt : inv (i + 1) accum₁ accum₂ := by
            simp [inv, lt'', inv₀]
          have invf : inv (i + 1) (accum₁ + 1) (accum₂ + 1) := by
            simp [inv, lt'', inv₀]
          cases ns.get ⟨i, hlt⟩ <;> simp
          . exact go invf hlt
          . exact go invt hlt
        . simp
          exact Nat.ne_of_lt lt'
    case inr nlt' =>
      have ge := Nat.ge_of_not_lt nlt'
      cases Nat.lt_or_eq_of_le ge with
      | inl gt =>
        have hlt : i < n := Nat.lt_trans gt lt
        have : i ≠ n := Nat.ne_of_lt hlt
        unfold count_unset.go
        simp [this]
        rw [NodeSet.get_set_ne]
        . have h : ¬ (i + 1 > x) := Nat.not_lt_of_ge gt
          have invt : inv (i + 1) accum₁ accum₂ := by
            simp [inv, h, inv₀]
          have invf : inv (i + 1) (accum₁ + 1) (accum₂ + 1) := by
            simp [inv, h, inv₀]
          cases ns.get ⟨i, hlt⟩ <;> simp
          . exact go invf hlt
          . exact go invt hlt
        . simp
          exact Nat.ne_of_gt gt
      | inr eq =>
        simp [eq.symm] at unset
        unfold count_unset.go
        have : i ≠ n := Nat.ne_of_lt (eq ▸ lt)
        simp [this, eq.symm, unset]
        have inv : inv (i + 1) accum₁ (accum₂ + 1) := by
          simp [inv, eq, inv₀]
        exact eq ▸ (go inv (eq ▸ lt))

  have inv₀ : inv 0 0 0 := by simp [inv, Nat.not_lt_zero x]
  have := go inv₀ (Nat.zero_le _)
  exact Nat.le_of_eq this
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

theorem NodeSet.get_empty {n : Nat} (i : Nat) (h : i < n) :
  (NodeSet.empty : NodeSet n).get ⟨i, h⟩ = false := by
  simp [empty, mkArray, NodeSet.get, Array.getElem_eq_data_get]

theorem NodeSet.clear_eq_empty (ns : NodeSet n) : ns.clear = NodeSet.empty := by
  have : ns.clear.val.size = n := ns.clear.property
  apply Subtype.ext
  apply Array.ext
  . simp [this, empty]
  . intro j h₁ h₂
    have h : j < n := ns.clear.property ▸ h₁
    have hc : ns.clear.get ⟨j, h⟩ = false := go ns 0 j (Nat.zero_le _) (Nat.zero_le _) h
    simp [NodeSet.get] at hc
    have he : empty.get ⟨j, h⟩ = false := NodeSet.get_empty j h
    simp [NodeSet.get] at he
    rw [hc, he]
where
  go (ns : NodeSet n) (i j : Nat) (hle : i ≤ n) (h₁ : i ≤ j) (h₂ : j < n) :
    (NodeSet.clear.go ns i hle).get ⟨j, h₂⟩ = false := by
    have h := go' ns i j hle h₂
    simp [h₁] at h
    exact h
  go' (ns : NodeSet n) (i j : Nat) (hle : i ≤ n) (h : j < n) :
    if i ≤ j then
      (NodeSet.clear.go ns i hle).get ⟨j, h⟩ = false
    else
      (NodeSet.clear.go ns i hle).get ⟨j, h⟩ = ns.get ⟨j, h⟩ := by
    split
    case inl le =>
      unfold NodeSet.clear.go
      split
      case inl eq =>
        subst eq
        exact absurd le (Nat.not_le_of_gt h)
      case inr neq =>
        simp
        have hlt : i < n := Nat.lt_of_le_of_ne hle neq
        have ih := go' (ns.unset ⟨i, hlt⟩) (i + 1) j hlt h
        cases Nat.lt_or_ge j (i + 1) with
        | inl lt =>
          have eq := Nat.eq_of_ge_of_lt le lt
          subst eq
          simp at ih
          exact ih
        | inr ge =>
          simp [ge] at ih
          exact ih
    case inr nle =>
      unfold NodeSet.clear.go
      split
      case inl eq => rfl
      case inr neq =>
        simp
        have hlt : i < n := Nat.lt_of_le_of_ne hle neq
        have ih := go' (ns.unset ⟨i, hlt⟩) (i + 1) j hlt h
        have : ¬ i + 1 ≤ j := by
          intro h
          exact absurd (Nat.le_trans (Nat.le_succ _) h) nle
        simp [this] at ih
        rw [ih]
        apply NodeSet.get_unset_ne
        simp
        apply Nat.ne_of_gt
        exact Nat.lt_of_not_ge nle
termination_by go' _ => n - i

open NFA

structure NodeSets (n : Nat) where
  visited : NodeSet n
  current : NodeSet n
deriving Repr

instance : ToString (NodeSets n) where
  toString ns := reprStr ns

def NodeSets.init (current : NodeSet n) : NodeSets n :=
  ⟨NodeSet.empty, current⟩

-- TODO: how to avoid allocating a pair?
-- TODO: check if the modifications don't cause copying
def addεClosure (nfa : NFA) (i : Nat) (sets : NodeSets nfa.nodes.size) :
  { sets' : NodeSets nfa.nodes.size // sets'.visited.count_unset ≤ sets.visited.count_unset } :=
  if hlt : i < nfa.nodes.size then
    let ⟨visited, ns⟩ := sets
    if hvis : visited.get ⟨i, hlt⟩ then
      ⟨⟨visited, ns⟩, by simp⟩
    else
      let visited' := visited.set ⟨i, hlt⟩
      have h : visited'.count_unset < visited.count_unset := visited.lt_count_unset hlt hvis
      let ns := ns.set ⟨i, hlt⟩
      match nfa[i] with
      | .epsilon next =>
        let sets' := addεClosure nfa next ⟨visited', ns⟩
        have h' : sets'.val.visited.count_unset ≤ visited.count_unset :=
          Nat.le_trans sets'.property (Nat.le_of_lt h)
        ⟨sets'.val, h'⟩
      | .split next₁ next₂ =>
        let sets' := addεClosure nfa next₁ ⟨visited', ns⟩
        have h' : sets'.val.visited.count_unset < visited.count_unset :=
          Nat.lt_of_le_of_lt sets'.property h
        let sets'' := addεClosure nfa next₂ sets'
        ⟨sets''.val, Nat.le_trans sets''.property (Nat.le_of_lt h')⟩
      | _ => ⟨⟨visited', ns⟩, Nat.le_of_lt h⟩
  else
    ⟨sets, by simp⟩
termination_by _ => sets.visited.count_unset

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

partial def NFA.NFA.match (nfa : NFA) (s : String) : Bool :=
  if h : 0 < nfa.nodes.size then
    let ns := addεClosure (dbgTraceVal nfa) nfa.start (NodeSets.init NodeSet.empty)
    let ns := go nfa s 0 ns.val.current
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
