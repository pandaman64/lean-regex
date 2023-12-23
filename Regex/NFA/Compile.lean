import Regex.Lemmas
import Regex.Regex
import Regex.NFA.Basic
import Regex.NFA.Order

namespace NFA

def NFA.addNode (nfa : NFA) (node : Node) :
  { nfa' : NFA // nfa ≤ nfa' } :=
  have isLt : nfa.nodes.size < (nfa.nodes.push node).size := by
    simp [Array.size_push]
  let start := nfa.nodes.size
  let nfa' : NFA := ⟨nfa.nodes.push node, ⟨start, isLt⟩⟩

  have property : nfa ≤ nfa' := by
    intro i h
    have h' : i < nfa'.nodes.size := Nat.lt_trans h isLt
    have eq : nfa'[i] = nfa[i] := by
      apply Array.get_push_lt
    exact ⟨h', Node.le_of_eq eq.symm⟩

  ⟨nfa', property⟩

theorem NFA.le_addNode {nfa : NFA} {node : Node} :
  nfa ≤ (nfa.addNode node).val := (nfa.addNode node).property

theorem NFA.lt_size_addNode {nfa : NFA} {node : Node} :
  nfa.nodes.size < (nfa.addNode node).val.nodes.size := (nfa.addNode node).val.start.isLt

theorem NFA.get_lt_addNode {nfa : NFA} {node : Node} (h : i < nfa.nodes.size) :
  (nfa.addNode node).val[i]'(Nat.lt_of_lt_of_le h (NFA.le_size_of_le NFA.le_addNode)) = nfa[i] :=
  Array.get_push_lt _ _ _ h

@[simp]
theorem NFA.get?_addNode {nfa : NFA} {node : Node} :
  (nfa.addNode node).val[(nfa.addNode node).val.start.val]? = some node := by
  simp [NFA.addNode]
  apply Array.get?_push_eq

@[simp]
theorem NFA.get_addNode {nfa : NFA} {node : Node} :
  (nfa.addNode node).val[(nfa.addNode node).val.start.val] = node := by
  simp [NFA.addNode]
  apply Array.get_push_eq

@[simp]
theorem NFA.get_addNode' {nfa : NFA} {node : Node} :
  (nfa.addNode node).val[nfa.nodes.size]'(NFA.lt_size_addNode) = node := by
  have : nfa.nodes.size = (nfa.addNode node).val.start.val := by
    simp [NFA.addNode]
  simp [this]

def compile (r : Regex) : NFA :=
  let result := loop r 0 ⟨#[.done], ⟨0, Nat.zero_lt_succ _⟩⟩
  result.val
where
  /--
    The main loop of the compilation.

    It compiles the given regex into nodes that transitions to `next` on match.
    Returned NFA contains the compiled nodes at the end and starts at the node
    corresponding to the given regex.
  -/
  loop (r : Regex) (next : Nat) (nfa : NFA) : { nfa' // nfa ≤ nfa' } := match r with
  | .empty => nfa.addNode .fail
  | .epsilon => nfa.addNode (.epsilon next)
  | .char c => nfa.addNode (.char c next)
  | .alternate r₁ r₂ =>
    -- TODO: it feels better to compile r₂ first to align with concat
    let nfa₁ := loop r₁ next nfa
    let start₁ := nfa₁.val.start
    let nfa₂ := loop r₂ next nfa₁
    let start₂ := nfa₂.val.start
    let nfa' := nfa₂.val.addNode (.split start₁ start₂)

    have property : nfa ≤ nfa' :=
      calc nfa
        _ ≤ nfa₁.val := nfa₁.property
        _ ≤ nfa₂.val := nfa₂.property
        _ ≤ nfa' := nfa'.property

    ⟨nfa', property⟩
  | .concat r₁ r₂ =>
    let nfa₂ := loop r₂ next nfa
    let nfa₁ := loop r₁ nfa₂.val.start nfa₂

    have property : nfa ≤ nfa₁ :=
      calc nfa
        _ ≤ nfa₂.val := nfa₂.property
        _ ≤ nfa₁.val := nfa₁.property

    ⟨nfa₁, property⟩
  | .star r =>
    -- We need to generate a placeholder node first. We use `fail` for it because
    -- 1. We'll use the fact that `fail` is a minimal element when strengthening induction hypotheis;
    -- 2. We want to make sure `done` does not appear except at the first node.
    -- 3. variants without data are represented as a boxed integer so there is one less allocation.
    -- TODO: check generated code
    let nfa' := nfa.addNode .fail
    let start := nfa'.val.start
    let nfa'' := loop r start nfa'

    have property : nfa ≤ nfa'' :=
      calc nfa
        _ ≤ nfa'.val := nfa'.property
        _ ≤ nfa''.val := nfa''.property
    have isLt : start.val < nfa''.val.nodes.size :=
      Nat.lt_of_lt_of_le nfa'.val.start.isLt (NFA.le_size_of_le nfa''.property)

    -- Patch the placeholder node
    let target := nfa''.val.start
    let nodes''' := nfa''.val.nodes.set ⟨start.val, isLt⟩ (.split target next)

    have eq_size : nodes'''.size = nfa''.val.nodes.size := by simp
    have isLt' : start.val < nodes'''.size := eq_size ▸ isLt
    let nfa''' := ⟨nodes''', ⟨start.val, isLt'⟩⟩

    have property' : nfa ≤ nfa''' := by
      intro i h

      have le_size : nfa.nodes.size ≤ nfa''.val.nodes.size := NFA.le_size_of_le property
      have h₂ : i < nodes'''.size := Nat.lt_of_lt_of_le h (eq_size ▸ le_size)
      exists h₂

      have eq : nfa'''[i] = nfa''.val[i]'(Nat.lt_of_lt_of_le h le_size) := by
        apply Array.get_set_ne
        exact (Nat.ne_of_gt h)
      rw [eq]
      exact (property i _).2

    ⟨nfa''', property'⟩

#eval compile (Regex.star (Regex.char 'a'))
#eval compile (Regex.alternate (Regex.char 'x') (Regex.star (Regex.concat (Regex.char 'a') (Regex.char 'b'))))
#eval compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))

-- Useful lemmas about the compilation
theorem compile.loop.le : nfa ≤ (compile.loop r next nfa).val :=
  (compile.loop r next nfa).property

theorem compile.loop.empty (eq : compile.loop .empty next nfa = result)
  {motive : result = nfa.addNode .fail → P} : P := by
  simp [compile.loop] at eq
  exact motive eq.symm

theorem compile.loop.epsilon (eq : compile.loop .epsilon next nfa = result)
  {motive : result = nfa.addNode (.epsilon next) → P} : P := by
  simp [compile.loop] at eq
  exact motive eq.symm

theorem compile.loop.char (eq : compile.loop (.char c) next nfa = result)
  {motive : result = nfa.addNode (.char c next) → P} : P := by
  simp [compile.loop] at eq
  exact motive eq.symm

theorem compile.loop.alternate (eq : compile.loop (Regex.alternate r₁ r₂) next nfa = result)
  {motive : ∀nfa₁ start₁ nfa₂ start₂ nfa' property,
    nfa₁ = compile.loop r₁ next nfa →
    start₁ = nfa₁.val.start →
    nfa₂ = compile.loop r₂ next nfa₁ →
    start₂ = nfa₂.val.start →
    nfa' = nfa₂.val.addNode (.split start₁ start₂) →
    result = ⟨nfa', property⟩ →
    P
  } : P := by
  let nfa₁ := loop r₁ next nfa
  let start₁ := nfa₁.val.start
  let nfa₂ := loop r₂ next nfa₁
  let start₂ := nfa₂.val.start
  let nfa' := nfa₂.val.addNode (.split start₁ start₂)

  have property : nfa ≤ nfa' :=
    calc nfa
      _ ≤ nfa₁.val := nfa₁.property
      _ ≤ nfa₂.val := nfa₂.property
      _ ≤ nfa' := nfa'.property

  have : result = ⟨nfa', property⟩ := by
    simp [eq.symm, compile.loop]
  exact motive nfa₁ start₁ nfa₂ start₂ nfa' property rfl rfl rfl rfl rfl this

theorem compile.loop.concat (eq : compile.loop (Regex.concat r₁ r₂) next nfa = result)
  {motive : ∀nfa₂ nfa₁ property,
    nfa₂ = compile.loop r₂ next nfa →
    nfa₁ = compile.loop r₁ nfa₂.val.start nfa₂ →
    result = ⟨nfa₁, property⟩ →
    P
  } : P := by
  let nfa₂ := loop r₂ next nfa
  let nfa₁ := loop r₁ nfa₂.val.start nfa₂

  have property : nfa ≤ nfa₁ :=
    calc nfa
      _ ≤ nfa₂.val := nfa₂.property
      _ ≤ nfa₁.val := nfa₁.property

  have : result = ⟨nfa₁, property⟩ := by
    simp [eq.symm, compile.loop]
  exact motive nfa₂ nfa₁ property rfl rfl this

theorem compile.loop.star (eq : compile.loop (Regex.star r) next nfa = result)
  {motive : ∀nfa' start nfa'' nodes''' nfa''' isLt isLt' property',
    nfa' = nfa.addNode .fail →
    start = nfa'.val.start →
    nfa'' = compile.loop r start nfa' →
    nodes''' = nfa''.val.nodes.set ⟨start.val, isLt⟩ (.split nfa''.val.start next) →
    nfa''' = ⟨nodes''', ⟨start.val, isLt'⟩⟩ →
    result = ⟨nfa''', property'⟩ →
    P
  } : P := by
  let nfa' := nfa.addNode .fail
  let start := nfa'.val.start
  let nfa'' := loop r start nfa'

  have property : nfa ≤ nfa'' :=
    calc nfa
      _ ≤ nfa'.val := nfa'.property
      _ ≤ nfa''.val := nfa''.property
  have isLt : start.val < nfa''.val.nodes.size :=
    Nat.lt_of_lt_of_le nfa'.val.start.isLt (NFA.le_size_of_le nfa''.property)

  -- Patch the placeholder node
  let nodes''' := nfa''.val.nodes.set ⟨start.val, isLt⟩ (.split nfa''.val.start next)

  have eq_size : nodes'''.size = nfa''.val.nodes.size := by simp
  have isLt' : start.val < nodes'''.size := eq_size ▸ isLt
  let nfa''' : NFA := ⟨nodes''', ⟨start.val, isLt'⟩⟩

  have property' : nfa ≤ nfa''' := by
    intro i h

    have le_size : nfa.nodes.size ≤ nfa''.val.nodes.size := NFA.le_size_of_le property
    have h₂ : i < nodes'''.size := Nat.lt_of_lt_of_le h (eq_size ▸ le_size)
    exists h₂

    have eq : nfa'''[i] = nfa''.val[i]'(Nat.lt_of_lt_of_le h le_size) := by
      apply Array.get_set_ne
      exact (Nat.ne_of_gt h)
    rw [eq]
    exact (property i _).2

  have : result = ⟨nfa''', property'⟩ := by
    simp [eq.symm, compile.loop]
  exact motive nfa' start nfa'' nodes''' nfa''' isLt isLt' property' rfl rfl rfl rfl rfl this

theorem compile.loop.get_lt (eq : compile.loop r next nfa = result)
  (h : i < nfa.nodes.size) :
  result.val[i]'(Nat.lt_of_lt_of_le h (NFA.le_size_of_le (eq ▸ compile.loop.le))) = nfa[i] := by
  induction r generalizing next nfa with
  | empty | epsilon | char =>
    try apply compile.loop.empty eq
    try apply compile.loop.epsilon eq
    try apply compile.loop.char eq
    intro eq
    subst eq
    apply NFA.get_lt_addNode h
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq

    have h' : i < nfa₁.val.nodes.size :=
      Nat.lt_of_lt_of_le h (NFA.le_size_of_le nfa₁.property)
    have h'' : i < nfa₂.val.nodes.size :=
      Nat.lt_of_lt_of_le h' (NFA.le_size_of_le nfa₂.property)

    simp [eq, eq₅, NFA.get_lt_addNode h'']
    simp [ih₂ eq₃.symm h']
    simp [ih₁ eq₁.symm h]
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    have h' : i < nfa₂.val.nodes.size :=
      Nat.lt_of_lt_of_le h (NFA.le_size_of_le nfa₂.property)

    simp [eq]
    simp [ih₁ eq₁.symm h']
    simp [ih₂ eq₂.symm h]
  | star r ih =>
    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq

    have h' : i < nfa'.val.nodes.size :=
      Nat.lt_of_lt_of_le h (NFA.le_size_of_le nfa'.property)
    have h'' : i < nfa''.val.nodes.size :=
      Nat.lt_of_lt_of_le h' (NFA.le_size_of_le nfa''.property)
    have ih := ih eq₃.symm h'
    have ne : (Fin.mk start isLt).val ≠ i := by
      simp [eq₂]
      rw [eq₁]
      simp [NFA.addNode]
      exact Nat.ne_of_gt h

    conv =>
      lhs
      simp [eq, eq₅, NFA.eq_get, eq₄]
      rw [Array.get_set_ne nfa''.val.nodes ⟨start, isLt⟩ _ h'' ne]
      simp [NFA.eq_get.symm, ih]
      simp [eq₁, NFA.get_lt_addNode h]

-- The compiled NFA contains `.done` only at the first position
theorem compile.loop.get_done_of_zero (eq : compile.loop r next nfa = result)
  (assm : ∀i, (_ : i < nfa.nodes.size) → nfa[i] = .done → i = 0) :
  ∀i, (_ : i < result.val.nodes.size) → result.val[i] = .done → i = 0 := by
  induction r generalizing next nfa with
  | empty | epsilon | char =>
    try apply compile.loop.empty eq
    try apply compile.loop.epsilon eq
    try apply compile.loop.char eq

    intro eq i h done
    subst eq
    cases Nat.lt_or_ge i nfa.nodes.size with
    | inl lt =>
      rw [NFA.get_lt_addNode lt] at done
      exact assm i lt done
    | inr ge =>
      simp [NFA.addNode] at h
      have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge h
      simp [this] at done
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq i h done

    have ih : i < nfa₂.val.nodes.size → i = 0 := by
      intro h'
      have done' : nfa₂.val[i] = .done := by
        simp [eq, eq₅, NFA.get_lt_addNode h'] at done
        exact done
      apply ih₂ eq₃.symm _ i h' done'
      exact ih₁ eq₁.symm assm

    cases Nat.lt_or_ge i nfa₂.val.nodes.size with
    | inl lt => exact ih lt
    | inr ge =>
      simp [eq, eq₅, NFA.addNode] at h
      have : i = nfa₂.val.nodes.size := Nat.eq_of_ge_of_lt ge h
      simp [this, eq, eq₅] at done
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    simp [eq]
    apply ih₁ eq₁.symm
    apply ih₂ eq₂.symm assm
  | star r ih =>
    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ _ eq₃ eq₄ eq₅ eq i h done

    have assm' : ∀i, (_ : i < nfa'.val.nodes.size) → nfa'.val[i] = .done → i = 0 := by
      intro i h done
      cases Nat.lt_or_ge i nfa.nodes.size with
      | inl lt =>
        simp [eq₁, NFA.get_lt_addNode lt] at done
        exact assm i lt done
      | inr ge =>
        simp [eq₁, NFA.addNode] at h
        have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge h
        simp [this, eq₁] at done
    have h' : i < nfa''.val.nodes.size := by
      simp [eq, eq₅, eq₄] at h
      exact h
    have ih := ih eq₃.symm assm' i h'

    simp [eq, eq₅, NFA.eq_get, eq₄, Array.get_set, h'] at done
    split at done
    . exact done.elim
    . exact ih done

theorem compile.get_done_iff_zero (eq : compile r = result) (h : i < result.nodes.size) :
  result[i] = .done ↔ i = 0 := by
  let init : NFA := ⟨#[.done], ⟨0, Nat.zero_lt_succ _⟩⟩
  generalize eq' : compile.loop r 0 init = result'
  have : result = result'.val := by
    simp [eq.symm, compile, eq'.symm]
  simp [this] at h
  simp [this]

  apply Iff.intro
  . intro done
    have assm : ∀i, (_ : i < init.nodes.size) → init[i] = .done → i = 0 := by
      intro i h _
      simp at h
      match i with
      | 0 => rfl
      | i + 1 => contradiction
    exact compile.loop.get_done_of_zero eq' assm i h done
  . intro h
    have h' : 0 < init.nodes.size := by decide
    simp [h, eq'.symm]
    apply compile.loop.get_lt rfl h'

end NFA
