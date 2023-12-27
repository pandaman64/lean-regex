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
  -- TODO: now I don't think we use NFA's ordering except for the size inequality.
  -- Just replace the condition.
  -- TODO: check all array insertions are handled linearly.
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
    -- 1. We want to make sure `done` does not appear except at the first node.
    -- 2. variants without data are represented as a boxed integer so there is one less allocation.
    -- TODO: check generated code
    let placeholder := nfa.addNode .fail
    let loopStart := placeholder.val.start
    let compiled := loop r loopStart placeholder

    -- have property : nfa ≤ compiled :=
    --   calc nfa
    --     _ ≤ placeholder.val := placeholder.property
    --     _ ≤ compiled.val := compiled.property
    have isLt : loopStart.val < compiled.val.nodes.size :=
      Nat.lt_of_lt_of_le placeholder.val.start.isLt (NFA.le_size_of_le compiled.property)

    -- Patch the placeholder node
    let target := compiled.val.start
    let nodes := compiled.val.nodes.set ⟨loopStart.val, isLt⟩ (.split target next)

    have eq_size : nodes.size = compiled.val.nodes.size := by simp
    have isLt' : loopStart.val < nodes.size := eq_size ▸ isLt
    let patched : NFA := ⟨nodes, ⟨loopStart.val, isLt'⟩⟩

    -- Add the start node
    -- Creating a split node with the same targets feels a bit waste
    let final := patched.addNode (.split loopStart loopStart)

    have property' : nfa ≤ final := by
      intro i h

      -- have le_size : nfa.nodes.size ≤ nfa''.val.nodes.size := NFA.le_size_of_le property
      -- have h₂ : i < nodes.size := Nat.lt_of_lt_of_le h (eq_size ▸ le_size)
      have h₂ : i < final.val.nodes.size := sorry
      exists h₂

      -- have eq : nfa'''[i] = nfa''.val[i]'(Nat.lt_of_lt_of_le h le_size) := by
      --   apply Array.get_set_ne
      --   exact (Nat.ne_of_gt h)
      -- rw [eq]
      -- exact (property i _).2
      sorry

    ⟨final, property'⟩

#eval compile (Regex.star (Regex.char 'a'))
#eval compile (Regex.alternate (Regex.char 'x') (Regex.star (Regex.concat (Regex.char 'a') (Regex.char 'b'))))
#eval compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))
#eval compile (Regex.concat (Regex.star (Regex.char 'a')) (Regex.star (Regex.char 'b')))

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
  {motive : ∀placeholder loopStart compiled nodes patched final isLt isLt' property',
    placeholder = nfa.addNode .fail →
    loopStart = placeholder.val.start →
    compiled = compile.loop r loopStart placeholder →
    nodes = compiled.val.nodes.set ⟨loopStart.val, isLt⟩ (.split compiled.val.start next) →
    patched = NFA.mk nodes ⟨loopStart.val, isLt'⟩ →
    final = patched.addNode (.split loopStart loopStart) →
    result = ⟨final, property'⟩ →
    P
  } : P := by
  let placeholder := nfa.addNode .fail
  let loopStart := placeholder.val.start
  let compiled := loop r loopStart placeholder

  have isLt : loopStart.val < compiled.val.nodes.size :=
    Nat.lt_of_lt_of_le placeholder.val.start.isLt (NFA.le_size_of_le compiled.property)

  -- Patch the placeholder node
  let target := compiled.val.start
  let nodes := compiled.val.nodes.set ⟨loopStart.val, isLt⟩ (.split target next)

  have eq_size : nodes.size = compiled.val.nodes.size := by simp
  have isLt' : loopStart.val < nodes.size := eq_size ▸ isLt
  let patched : NFA := ⟨nodes, ⟨loopStart.val, isLt'⟩⟩

  -- Add the start node
  -- Creating a split node with the same targets feels a bit waste
  let final := patched.addNode (.split loopStart loopStart)

  have property' : nfa ≤ final := sorry

  have : result = ⟨final, property'⟩ := by
    simp [eq.symm, compile.loop]
  exact motive placeholder loopStart compiled nodes patched final isLt isLt' property'
    rfl rfl rfl rfl rfl rfl this

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
    intro placeholder loopStart compiled nodes patched final isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq

    have h' : i < placeholder.val.nodes.size :=
      Nat.lt_of_lt_of_le h (NFA.le_size_of_le placeholder.property)
    have h'' : i < compiled.val.nodes.size :=
      Nat.lt_of_lt_of_le h' (NFA.le_size_of_le compiled.property)
    have h''' : i < patched.nodes.size := by
      simp [eq₅, eq₄]
      exact h''
    have ne : (Fin.mk loopStart isLt).val ≠ i := by
      simp [eq₂]
      rw [eq₁]
      simp [NFA.addNode]
      exact Nat.ne_of_gt h
    have ih := ih eq₃.symm h'

    conv =>
      lhs
      simp [eq, eq₆, eq₅]
      rw [NFA.get_lt_addNode h''', NFA.eq_get]
      simp [eq₅, eq₄]
      rw [Array.get_set_ne compiled.val.nodes ⟨loopStart, isLt⟩ _ h'' ne]
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
    intro placeholder loopStart compiled nodes patched final isLt isLt' property'
      eq₁ _ eq₃ eq₄ eq₅ eq₆ eq i h done

    have assm' : ∀i, (_ : i < placeholder.val.nodes.size) → placeholder.val[i] = .done → i = 0 := by
      intro i h done
      cases Nat.lt_or_ge i nfa.nodes.size with
      | inl lt =>
        simp [eq₁, NFA.get_lt_addNode lt] at done
        exact assm i lt done
      | inr ge =>
        simp [eq₁, NFA.addNode] at h
        have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge h
        simp [this, eq₁] at done
    cases Nat.lt_or_ge i compiled.val.nodes.size with
    | inl h' =>
      have h'' : i < patched.nodes.size := by
        simp [eq₅, eq₄]
        exact h'
      have ih := ih eq₃.symm assm' i h'

      simp [eq, eq₆] at done
      have done : patched[i] = .done := by
        rw [NFA.get_lt_addNode h''] at done
        exact done
      simp [eq₅, NFA.eq_get, eq₄, Array.get_set, h'] at done
      split at done
      . exact done.elim
      . exact ih done
    | inr ge =>
      simp [eq, eq₆, NFA.addNode, eq₅, eq₄] at h
      have : i = compiled.val.nodes.size := Nat.eq_of_ge_of_lt ge h
      have : i = patched.nodes.size := by
        simp [eq₅, eq₄]
        exact this
      simp [this, eq, eq₆] at done

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

theorem compile.loop.inBounds (eq : compile.loop r next nfa = result)
  (h₁ : next < nfa.nodes.size) (h₂ : nfa.inBounds) :
  result.val.inBounds := by
  induction r generalizing next nfa with
  | empty | epsilon | char =>
    try apply compile.loop.empty eq
    try apply compile.loop.epsilon eq
    try apply compile.loop.char eq

    intro eq i
    subst eq
    have h' : next < nfa.nodes.size + 1 := lt_trans h₁ (Nat.lt_succ_self _)

    cases Nat.lt_or_ge i nfa.nodes.size with
    | inl lt =>
      simp [NFA.get_lt_addNode lt]
      exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) (by simp [NFA.addNode]; exact Nat.le_succ _)
    | inr ge =>
      let lt := i.isLt
      simp only [NFA.addNode, Array.size_push] at lt
      have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge lt
      simp [this]
      try simp [NFA.addNode]
      try exact Node.inBounds.epsilon h'
      try exact Node.inBounds.char h'
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq i

    have ih : i < nfa₂.val.nodes.size → result.val[i].inBounds result.val.nodes.size := by
      intro h
      simp [eq, eq₅]
      simp [NFA.get_lt_addNode h]
      simp [NFA.addNode]
      have ih₁ := ih₁ eq₁.symm h₁ h₂
      have ih₂ := ih₂ eq₃.symm (Nat.lt_of_lt_of_le h₁ (NFA.le_size_of_le nfa₁.property)) ih₁
      exact Node.inBounds_of_inBounds_of_le (ih₂ ⟨i, h⟩) (Nat.le_succ _)

    cases Nat.lt_or_ge i nfa₂.val.nodes.size with
    | inl lt => exact ih lt
    | inr ge =>
      let lt := i.isLt
      simp only [eq, eq₅, NFA.addNode, Array.size_push] at lt
      have : i = nfa₂.val.nodes.size := Nat.eq_of_ge_of_lt ge lt
      simp [eq, eq₅, this]
      simp [NFA.addNode]
      apply Node.inBounds.split
      . exact lt_trans start₁.isLt (Nat.lt_of_le_of_lt (NFA.le_size_of_le nfa₂.property) (Nat.lt_succ_self _))
      . exact lt_trans start₂.isLt (Nat.lt_succ_self _)
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    simp [eq]
    apply ih₁ eq₁.symm nfa₂.val.start.isLt
    apply ih₂ eq₂.symm h₁ h₂
  | star r ih =>
    apply compile.loop.star eq
    intro placeholder loopStart compiled nodes patched final isLt isLt' property'
      eq₁ _ eq₃ eq₄ eq₅ eq₆ eq i

    have inBounds' : placeholder.val.inBounds := by
      simp [eq₁]
      intro i
      cases Nat.lt_or_ge i nfa.nodes.size with
      | inl lt =>
        simp [NFA.get_lt_addNode lt]
        exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) (by simp [NFA.addNode]; exact Nat.le_succ _)
      | inr ge =>
        let lt := i.isLt
        simp only [NFA.addNode, Array.size_push] at lt
        have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge lt
        simp [this]
    have ih := ih eq₃.symm loopStart.isLt inBounds'

    cases Nat.lt_or_ge i patched.nodes.size with
    | inl lt =>
      have hj : i < compiled.val.nodes.size := by
        simp [eq₅, eq₄] at lt
        exact lt
      have : result.val[i] = patched.nodes[i] := by
        simp [eq, eq₆, NFA.get_lt_addNode lt]
        exact NFA.eq_get
      rw [this]
      simp [eq₅, eq₄]
      rw [Array.get_set _ _ _ hj]
      have h' : compiled.val.nodes.size ≤ result.val.nodes.size := by
        simp [eq, eq₆, NFA.addNode, eq₅, eq₄]
        exact Nat.le_succ _
      split
      . apply Node.inBounds.split
        . calc compiled.val.start.val
            _ < compiled.val.nodes.size := compiled.val.start.isLt
            _ ≤ _ := h'
        . calc next
            _ < nfa.nodes.size := h₁
            _ ≤ placeholder.val.nodes.size := NFA.le_size_of_le placeholder.property
            _ ≤ compiled.val.nodes.size := NFA.le_size_of_le compiled.property
            _ ≤ _ := h'
      . exact Node.inBounds_of_inBounds_of_le (ih ⟨i, hj⟩) h'
    | inr ge =>
      have h : loopStart < patched.nodes.size + 1 :=
        calc loopStart.val
          _ < placeholder.val.nodes.size := loopStart.isLt
          _ ≤ compiled.val.nodes.size := NFA.le_size_of_le compiled.property
          _ = patched.nodes.size := by simp [eq₅, eq₄]
          _ < _ := Nat.lt_succ_self _
      have lt : i < patched.nodes.size + 1 := by
        have : i < result.val.nodes.size := i.isLt
        simp [eq, eq₆, NFA.addNode] at this
        exact this
      have : i = patched.nodes.size := Nat.eq_of_ge_of_lt ge lt
      simp [this, eq, eq₆]
      simp [NFA.addNode]
      apply Node.inBounds.split <;> exact h

theorem compile.inBounds (eq : compile r = result) : result.inBounds := by
  let init : NFA := ⟨#[.done], ⟨0, Nat.zero_lt_succ _⟩⟩
  have h₁ : 0 < init.nodes.size := by decide
  have h₂ : init.inBounds := by
    simp
    intro i
    simp [NFA.eq_get, Array.singleton_get']
  simp [eq.symm, compile]
  exact compile.loop.inBounds rfl h₁ h₂

-- When we compile a new regex into an existing NFA, the compiled nodes first
-- "circulates" within the new nodes, then "escape" to the `next` node.

def compile.loop.NewNodesRange (_ : compile.loop r next nfa = result) : Set Nat :=
  { i | nfa.nodes.size ≤ i ∧ i < result.val.nodes.size }

theorem compile.loop.start_in_NewNodesRange (eq : compile.loop r next nfa = result) :
  result.val.start.val ∈ NewNodesRange eq := by
  simp [NewNodesRange]
  induction r generalizing next nfa with
  | empty =>
    apply compile.loop.empty eq
    intro eq
    rw [eq]
    simp [NFA.addNode]
  | epsilon =>
    apply compile.loop.epsilon eq
    intro eq
    rw [eq]
    simp [NFA.addNode]
  | char c =>
    apply compile.loop.char eq
    intro eq
    rw [eq]
    simp [NFA.addNode]
  | alternate r₁ r₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property _ _ _ _ eq₅ eq
    rw [eq]
    simp
    rw [eq₅]
    simp [NFA.addNode]
    exact NFA.le_size_of_le (le_trans nfa₁.property nfa₂.property)
  | concat r₁ r₂ ih₁ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property _ eq₁ eq
    rw [eq]
    simp
    have ih₁ := ih₁ eq₁.symm
    exact le_trans (NFA.le_size_of_le nfa₂.property) ih₁
  | star r =>
    apply compile.loop.star eq
    intro placeholder loopStart compiled nodes patched final isLt isLt' property'
      _ _ _ eq₄ eq₅ eq₆ eq
    rw [eq]
    simp
    rw [eq₆, eq₅]
    simp [NFA.addNode, eq₄]
    calc nfa.nodes.size
      _ ≤ placeholder.val.nodes.size := NFA.le_size_of_le placeholder.property
      _ ≤ compiled.val.nodes.size := NFA.le_size_of_le compiled.property

theorem compile.loop.step_range (c : Char) (eq : compile.loop r next nfa = result) :
  ∀i, nfa.nodes.size ≤ i → (_ : i < result.val.nodes.size) →
  -- TODO: bind c here
  result.val[i].charStep c ⊆ {next} ∪ NewNodesRange eq ∧
  result.val[i].εStep ⊆ {next} ∪ NewNodesRange eq := by
  induction r generalizing next nfa with
  | empty =>
    apply compile.loop.empty eq
    intro eq i h₁ h₂
    simp [eq, NFA.addNode] at h₂
    have h : i = nfa.nodes.size := Nat.eq_of_ge_of_lt h₁ h₂
    simp [eq, h, Node.charStep, Node.εStep]
  | epsilon =>
    apply compile.loop.epsilon eq
    intro eq i h₁ h₂
    simp [eq, NFA.addNode] at h₂
    have h : i = nfa.nodes.size := Nat.eq_of_ge_of_lt h₁ h₂
    simp [eq, h, Node.charStep, Node.εStep]
  | char c' =>
    apply compile.loop.char eq
    intro eq i h₁ h₂
    simp [eq, NFA.addNode] at h₂
    have h : i = nfa.nodes.size := Nat.eq_of_ge_of_lt h₁ h₂
    simp [eq, h, Node.charStep, Node.εStep]
    apply le_trans
    . show (if c = c' then {next} else ∅) ≤ {next}
      simp
    . simp
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ eq₂ eq₃ eq₄ eq₅ eq i h₁ h₂
    simp [NewNodesRange, eq]

    have size : i < nfa'.val.nodes.size := by
      simp [eq] at h₂
      exact h₂
    have size₂ : nfa₂.val.nodes.size < nfa'.val.nodes.size := by
      simp [eq₅]
      exact NFA.lt_size_addNode
    have size₁ : nfa₁.val.nodes.size < nfa'.val.nodes.size :=
      Nat.lt_of_le_of_lt (NFA.le_size_of_le nfa₂.property) size₂

    cases Nat.lt_or_ge i nfa₁.val.nodes.size with
    | inl lt =>
      have ih₁ := ih₁ eq₁.symm i h₁ lt
      have : nfa'.val[i] = nfa₁.val[i] := by
        simp [eq₅]
        rw [NFA.get_lt_addNode (Nat.lt_of_lt_of_le lt (NFA.le_size_of_le nfa₂.property))]
        rw [get_lt eq₃.symm lt]
      rw [this]
      have : {next} ∪ NewNodesRange eq₁.symm ⊆
        {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa'.val.nodes.size} := by
        apply Set.insert_subset_insert
        apply Set.setOf_subset_setOf.mpr
        intro i h
        exact ⟨h.left, lt_trans h.right size₁⟩
      exact ⟨le_trans ih₁.left this, le_trans ih₁.right this⟩
    | inr ge =>
      cases Nat.lt_or_ge i nfa₂.val.nodes.size with
      | inl lt =>
        have ih₂ := ih₂ eq₃.symm i ge lt
        have : nfa'.val[i] = nfa₂.val[i] := by
          simp [eq₅]
          rw [NFA.get_lt_addNode lt]
        rw [this]
        have : {next} ∪ NewNodesRange eq₃.symm ⊆
          {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa'.val.nodes.size} := by
          apply Set.insert_subset_insert
          apply Set.setOf_subset_setOf.mpr
          intro i h
          exact ⟨le_trans (NFA.le_size_of_le nfa₁.property) h.left, lt_trans h.right size₂⟩
        exact ⟨le_trans ih₂.left this, le_trans ih₂.right this⟩
      | inr ge =>
        simp [eq, eq₅, NFA.addNode] at h₂
        have h : i = nfa₂.val.nodes.size := Nat.eq_of_ge_of_lt ge h₂
        have : nfa'.val[i] = (.split nfa₁.val.start nfa₂.val.start) := by
          simp [eq₅, h, eq₂, eq₄]
        simp [this, Node.charStep, Node.εStep]
        apply Set.insert_subset
        . simp
          have h := start_in_NewNodesRange eq₁.symm
          exact .inr ⟨h.left, lt_trans h.right size₁⟩
        . simp
          have h := start_in_NewNodesRange eq₃.symm
          exact .inr ⟨le_trans (NFA.le_size_of_le nfa₁.property) h.left, lt_trans h.right size₂⟩
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq i h₁ h₂
    simp [NewNodesRange, eq]

    have size : i < nfa₁.val.nodes.size := by
      simp [eq] at h₂
      exact h₂
    have size' : nfa₂.val.nodes.size ≤ nfa₁.val.nodes.size :=
      NFA.le_size_of_le nfa₁.property

    cases Nat.lt_or_ge i nfa₂.val.nodes.size with
    | inl lt =>
      have ih₂ := ih₂ eq₂.symm i h₁ lt
      have : nfa₁.val[i] = nfa₂.val[i] := get_lt eq₁.symm lt
      rw [this]
      have : {next} ∪ NewNodesRange eq₂.symm ⊆
        {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa₁.val.nodes.size} := by
        apply Set.insert_subset_insert
        apply Set.setOf_subset_setOf.mpr
        intro i h
        exact ⟨h.left, Nat.lt_of_lt_of_le h.right size'⟩
      exact ⟨le_trans ih₂.left this, le_trans ih₂.right this⟩
    | inr ge =>
      have ih₁ := ih₁ eq₁.symm i ge size
      have : {nfa₂.val.start.val} ∪ NewNodesRange eq₁.symm ⊆
        {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa₁.val.nodes.size} := by
        apply Set.union_subset
        . simp
          have h := start_in_NewNodesRange eq₂.symm
          exact .inr ⟨h.left, Nat.lt_of_lt_of_le h.right size'⟩
        . simp [Set.subset_def]
          intro i h
          exact .inr ⟨le_trans (NFA.le_size_of_le nfa₂.property) h.left, h.right⟩
      exact ⟨le_trans ih₁.left this, le_trans ih₁.right this⟩
  | star r ih =>
    apply compile.loop.star eq
    intro placeholder loopStart compiled nodes patched final isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq₆ eq i h₁ h₂
    simp [NewNodesRange, eq]

    have : i < final.val.nodes.size := by
      simp [eq] at h₂
      exact h₂

    cases Nat.lt_or_ge i placeholder.val.nodes.size with
    | inl lt =>
      simp [eq₁, NFA.addNode] at lt
      have h := Nat.eq_of_ge_of_lt h₁ lt
      have : final.val[i] = .split compiled.val.start next := by
        have : i = loopStart := by
          simp [eq₂]
          rw [eq₁]
          simp [NFA.addNode]
          exact h
        simp [this, eq₆]
        have : loopStart.val < patched.nodes.size :=
          calc loopStart.val
            _ < nodes.size := isLt'
            _ = patched.nodes.size := by simp [eq₅, eq₄]
        simp [NFA.get_lt_addNode this]
        simp [eq₅, NFA.eq_get, eq₄]
      simp [this, Node.charStep, Node.εStep]
      apply Set.insert_subset
      . have h := start_in_NewNodesRange eq₃.symm
        simp
        refine .inr ⟨le_trans (NFA.le_size_of_le placeholder.property) h.left, ?_⟩
        calc compiled.val.start.val
          _ < compiled.val.nodes.size := compiled.val.start.isLt
          _ ≤ patched.nodes.size := by simp [eq₅, eq₄]
          _ < _ := by simp [eq₆, NFA.addNode]
      . simp
    | inr ge =>
      cases Nat.lt_or_ge i compiled.val.nodes.size with
      | inl lt =>
        have ih := ih eq₃.symm i ge lt
        have : i < patched.nodes.size := by
          simp [eq₅, eq₄]
          exact lt
        simp [eq₆]
        rw [NFA.get_lt_addNode this]
        simp [NFA.eq_get, eq₅, eq₄]
        have ne : (Fin.mk loopStart isLt).val ≠ i := Nat.ne_of_lt (Nat.lt_of_lt_of_le loopStart.isLt ge)
        rw [Array.get_set_ne _ _ _ lt ne]
        simp [NFA.addNode]
        have : {loopStart.val} ∪ NewNodesRange eq₃.symm ⊆
          {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < patched.nodes.size + 1} := by
          apply Set.union_subset
          . simp [eq₂]
            rw [eq₁]
            simp [NFA.addNode]
            apply Or.inr
            calc nfa.nodes.size
              _ ≤ placeholder.val.nodes.size := NFA.le_size_of_le placeholder.property
              _ ≤ compiled.val.nodes.size := NFA.le_size_of_le compiled.property
              _ ≤ patched.nodes.size := by simp [eq₅, eq₄]
              _ < _ := by simp [eq₆, NFA.addNode]
          . simp [Set.subset_def]
            intro i h
            refine .inr ⟨le_trans (NFA.le_size_of_le placeholder.property) h.left, ?_⟩
            calc
              i < compiled.val.nodes.size := h.right
              _ ≤ patched.nodes.size := by simp [eq₅, eq₄]
              _ < _ := Nat.lt_succ_self _
        exact ⟨le_trans ih.left this, le_trans ih.right this⟩
      | inr ge =>
        have ge : i ≥ patched.nodes.size := by
          simp [eq₅, eq₄]
          exact ge
        have lt : i < patched.nodes.size + 1 := by
          simp [eq, eq₆, NFA.addNode] at h₂
          exact h₂
        have : i = patched.nodes.size := Nat.eq_of_ge_of_lt ge lt
        simp [eq₆, this, Node.charStep, Node.εStep]
        simp [NFA.addNode]
        apply Or.inr
        apply And.intro
        . rw [eq₂, eq₁]
          simp [NFA.addNode]
        . calc loopStart.val
            _ < nodes.size := isLt'
            _ = patched.nodes.size := by simp [eq₅, eq₄]
            _ < _ := by simp [eq₆, NFA.addNode]

-- TODO: prove no edge to the start

end NFA
