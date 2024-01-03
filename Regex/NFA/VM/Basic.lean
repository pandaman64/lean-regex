import Regex.Lemmas
import Regex.NFA.Basic

def Array.back' (a : Array α) (hemp : ¬ a.isEmpty) : α :=
  have : 0 < a.size := by
    simp [isEmpty] at hemp
    exact Nat.zero_lt_of_ne_zero hemp
  have : a.size - 1 < a.size := Nat.sub_lt_of_pos_le (by decide) this
  a[a.size - 1]

theorem Array.lt_size_of_pop_of_not_empty (a : Array α) (hemp : ¬ a.isEmpty) :
  (a.pop).size < a.size := by
  have : 0 < a.size := by
    simp [isEmpty] at hemp
    exact Nat.zero_lt_of_ne_zero hemp
  have : a.size - 1 < a.size := Nat.sub_lt_of_pos_le (by decide) this
  simp [Array.pop]
  exact this

namespace NFA.VM

-- TODO: use a bitvec?
abbrev NodeSet (n : Nat) := { array : Array Bool // array.size = n }

def NodeSet.empty {n : Nat} : NodeSet n :=
  ⟨mkArray n false, by simp⟩

def NodeSet.get (ns : NodeSet n) (i : Fin n) : Bool :=
  ns.val.get (i.cast ns.property.symm)

instance : GetElem (NodeSet n) Nat Bool (fun _ i => i < n) where
  getElem ns i h := ns.get ⟨i, h⟩

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

theorem NodeSet.get_set_set {ns : NodeSet n} {i j : Fin n} (set : ns.get i) :
  (ns.set j).get i := by
  cases decEq j i with
  | isTrue eq => exact eq ▸ NodeSet.get_set_eq _ _
  | isFalse neq =>
    have : j.val ≠ i.val := by
      intro h
      exact absurd (Fin.eq_of_val_eq h) neq
    rw [NodeSet.get_set_ne _ _ _ this]
    . exact set

theorem NodeSet.get_set {ns : NodeSet n} {i j : Fin n} :
  (ns.set j).get i = if j = i then true else ns.get i := by
  cases decEq j i with
  | isTrue eq => simp [eq]
  | isFalse neq =>
    simp [neq]
    apply NodeSet.get_set_ne
    intro h
    exact absurd (Fin.eq_of_val_eq h) neq

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

@[simp]
theorem NodeSet.get_empty {n : Nat} (i : Fin n) :
  (NodeSet.empty : NodeSet n).get i = false := by
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
    have he : empty.get ⟨j, h⟩ = false := NodeSet.get_empty ⟨j, h⟩
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

-- NOTE: this should overwrite to ns₁ if it's unique
def NodeSet.merge (ns₁ ns₂ : NodeSet n) : NodeSet n :=
  go ns₁ ns₂ 0 (Nat.zero_le _)
where
  go (ns₁ ns₂ : NodeSet n) (i : Nat) (hle : i ≤ n) : NodeSet n :=
    if h : i = n then
      ns₁
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      let ns₁ := if ns₂.get ⟨i, hlt⟩ then ns₁.set ⟨i, hlt⟩ else ns₁
      go ns₁ ns₂ (i + 1) hlt
termination_by go _ => n - i

theorem NodeSet.merge_get {ns₁ ns₂ : NodeSet n} {x : Fin n} :
  (ns₁.merge ns₂).get x = (ns₁.get x || ns₂.get x) := by
  let inv (ns₁ : NodeSet n) (i : Nat) : Prop :=
    ∀ j : Fin n, j < i → ns₁.get j = (ns₁.get j || ns₂.get j)

  let rec go (ns₁ : NodeSet n) (i : Nat) (hle : i ≤ n) (inv₀ : inv ns₁ i) :
    ∀ j : Fin n, (merge.go ns₁ ns₂ i hle).get j = (ns₁.get j || ns₂.get j) := by
    cases decEq i n with
    | isTrue h =>
      unfold merge.go
      simp [h]
      simp [h] at inv₀
      exact inv₀
    | isFalse h =>
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      unfold merge.go
      simp [h]
      set ns₁' := if ns₂.get ⟨i, hlt⟩ then ns₁.set ⟨i, hlt⟩ else ns₁
      have inv' : inv ns₁' (i + 1) := by
        intro j hj
        have : j ≤ i := Nat.le_of_succ_le_succ hj
        cases Nat.lt_or_eq_of_le this with
        | inl lt =>
          have := inv₀ j lt
          simp
          cases ns₂.get ⟨i, hlt⟩ with
          | true =>
            simp
            rw [NodeSet.get_set_ne]
            . exact this
            . exact Nat.ne_of_gt lt
          | false =>
            simp
            exact this
        | inr eq =>
          simp [eq.symm]
          split
          case inl _ => simp
          case inr h => simp [h]
      have ih := go ns₁' (i + 1) hlt inv'

      intro j
      rw [ih j]
      cases decEq i j with
      | isTrue eq =>
        simp [eq]
        split
        case inl h => simp [h]
        case inr _ => rfl
      | isFalse neq =>
        simp
        split
        case inl _ =>
          rw [NodeSet.get_set_ne]
          simp [neq]
        case inr _ => rfl

  have inv₀ : inv ns₁ 0 := by
    intro j hlt
    exact absurd hlt (Nat.not_lt_zero _)
  have := go ns₁ 0 (Nat.zero_le _) inv₀
  apply this
termination_by go _ => n - i

open NFA

-- TODO: check if the modifications don't cause copying
def εClosureTR (nfa : NFA) (inBounds : nfa.inBounds)
  (visited : NodeSet nfa.nodes.size) (stack : Array (Fin nfa.nodes.size)) :
  NodeSet nfa.nodes.size :=
  if hemp : stack.isEmpty then
    visited
  else
    let i := stack.back' hemp
    let stack' := stack.pop
    have : stack'.size < stack.size := Array.lt_size_of_pop_of_not_empty _ hemp
    if hvis : visited.get i then
      εClosureTR nfa inBounds visited stack'
    else
      let visited' := visited.set i
      have : visited'.count_unset < visited.count_unset := visited.lt_count_unset i.isLt hvis
      have inBounds' := (inBounds i).right
      let stack'' :=
        match hn : nfa[i] with
        | .epsilon next =>
          have h : next < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [Node.εStep] at inBounds'
            exact inBounds'

          stack'.push ⟨next, h⟩
        | .split next₁ next₂ =>
          have h₁ : next₁ < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [Node.εStep] at inBounds'
            apply Set.mem_of_mem_of_subset (by simp) inBounds'
          have h₂ : next₂ < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [Node.εStep] at inBounds'
            apply Set.mem_of_mem_of_subset (by simp) inBounds'

          (stack'.push ⟨next₁, h₁⟩).push ⟨next₂, h₂⟩
        | _ => stack'
      εClosureTR nfa inBounds visited' stack''
termination_by _ => (visited.count_unset, stack.size)

def charStepTR (nfa : NFA) (inBounds : nfa.inBounds) (c : Char) (init : NodeSet nfa.nodes.size) :
  NodeSet nfa.nodes.size := go nfa inBounds c init .empty 0 (Nat.zero_le _)
where
  go (nfa : NFA) (inBounds : nfa.inBounds) (c : Char) (init : NodeSet nfa.nodes.size)
    (accum : NodeSet nfa.nodes.size) (i : Nat) (hle : i ≤ nfa.nodes.size) :
    NodeSet nfa.nodes.size :=
    if h : i = nfa.nodes.size then
      accum
    else
      have hlt : i < nfa.nodes.size := Nat.lt_of_le_of_ne hle h
      let accum := if init.get ⟨i, hlt⟩ then
        match hn : nfa[i] with
        | .char c' next =>
          if c = c' then
            have : next < nfa.nodes.size := by
              have := (inBounds ⟨i, hlt⟩).left c'
              apply Set.mem_of_mem_of_subset _ this
              simp [hn, Node.charStep]
            -- TODO: reuse visited and stack
            accum.merge (εClosureTR nfa inBounds .empty #[⟨next, this⟩])
          else
            accum
        | _ => accum
      else accum
      go nfa inBounds c init accum (i + 1) hlt
termination_by go _ => nfa.nodes.size - i

end NFA.VM

open NFA.VM

partial def NFA.NFA.match (nfa : NFA) (inBounds : nfa.inBounds) (s : String) : Bool :=
  if h : 0 < nfa.nodes.size then
    let ns := εClosureTR (dbgTraceVal nfa) inBounds .empty #[nfa.start]
    let ns := go nfa inBounds s 0 ns
    -- This assumes that the first node is the accepting node
    ns.get ⟨0, h⟩
  else
    false
where
  go (nfa : NFA) (inBounds : nfa.inBounds) (s : String) (i : String.Pos) (ns : NodeSet nfa.nodes.size) : NodeSet nfa.nodes.size :=
    if s.atEnd i then
      ns
    else
      let c := s.get i
      let ns' := charStepTR nfa inBounds c ns
      dbgTrace s!"{ns} ⟶{c} {ns'}" (fun () => go nfa inBounds s (s.next i) ns')
