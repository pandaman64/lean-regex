import Regex.NFA.Compile
import RegexCorrectness.NFA.Order

namespace NFA

theorem compile.loop.get_lt (eq : compile.loop r next nfa = result)
  (h : i < nfa.nodes.size) :
  result.val[i]'(Nat.lt_of_lt_of_le h result.property) = nfa[i] := by
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
      Nat.lt_of_lt_of_le h nfa₁.property
    have h'' : i < nfa₂.val.nodes.size :=
      Nat.lt_of_lt_of_le h' nfa₂.property

    simp [eq, eq₅, NFA.get_lt_addNode h'']
    simp [ih₂ eq₃.symm h']
    simp [ih₁ eq₁.symm h]
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    have h' : i < nfa₂.val.nodes.size :=
      Nat.lt_of_lt_of_le h nfa₂.property

    simp [eq]
    simp [ih₁ eq₁.symm h']
    simp [ih₂ eq₂.symm h]
  | star r ih =>
    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq

    have h' : i < nfa'.val.nodes.size :=
      Nat.lt_of_lt_of_le h nfa'.property
    have h'' : i < nfa''.val.nodes.size :=
      Nat.lt_of_lt_of_le h' nfa''.property
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
  let init : NFA := compile.init
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

theorem compile.init.get : compile.init[0] = .done := by
  simp [compile.init, NFA.eq_get, Array.singleton_get']

theorem NFA.le_addNode {nfa : NFA} {node : Node} :
  nfa ≤ (nfa.addNode node).val := by
  intro i h
  have : i < (nfa.addNode node).val.nodes.size := by
    simp
    exact Nat.lt_of_lt_of_le h (Nat.le_succ _)
  exists this
  rw [NFA.get_lt_addNode]

theorem compile.loop.le : nfa ≤ (compile.loop r next nfa).val := by
  induction r generalizing next nfa with
  | empty | epsilon | char _ => unfold loop; exact NFA.le_addNode
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate (rfl : loop (.alternate r₁ r₂) next nfa = _)
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq
    rw [eq]
    calc nfa
      _ ≤ nfa₁.val := eq₁ ▸ ih₁
      _ ≤ nfa₂.val := eq₃ ▸ ih₂
      _ ≤ nfa'.val := eq₅ ▸ NFA.le_addNode
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat (rfl : loop (.concat r₁ r₂) next nfa = _)
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    rw [eq]
    calc nfa
      _ ≤ nfa₂.val := eq₂ ▸ ih₂
      _ ≤ nfa₁.val := eq₁ ▸ ih₁
  | star r ih =>
    apply compile.loop.star (rfl : loop (.star r) next nfa = _)
    intro placeholder loopStart compiled nodes patched isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq
    rw [eq]
    calc nfa
      _ ≤ placeholder.val := eq₁ ▸ NFA.le_addNode
      _ ≤ compiled.val := eq₃ ▸ ih
      _ ≤ patched := by
        intro i h
        simp [eq₅, eq₄]
        exists h
        simp [NFA.eq_get, eq₄, Array.get_set (hj := h)]
        split <;> try simp
        next eq =>
          subst eq
          calc compiled.val.nodes[loopStart.val]
            _ = .fail := by
              have := compile.loop.get_lt eq₃.symm loopStart.isLt
              rw [NFA.eq_get] at this
              rw [this, eq₂, eq₁]
              simp
            _ ≤ .split _ _ := by simp

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
    exact le_trans nfa₁.property nfa₂.property
  | concat r₁ r₂ ih₁ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property _ eq₁ eq
    rw [eq]
    simp
    have ih₁ := ih₁ eq₁.symm
    exact le_trans nfa₂.property ih₁
  | star r =>
    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ eq₂ _ _ eq₅ eq
    rw [eq]
    simp
    rw [eq₅]
    simp [eq₂]
    rw [eq₁]
    simp [NFA.addNode]

theorem compile.start_gt (eq : compile r = nfa) : 0 < nfa.start.val := by
  generalize eq' : compile.loop r 0 compile.init = result
  have : nfa = result.val := by
    simp [eq.symm, compile, eq'.symm]
  rw [this]
  have inRange := compile.loop.start_in_NewNodesRange eq'
  simp [compile.loop.NewNodesRange, compile.init] at inRange
  exact inRange

theorem compile.loop.step_range (eq : compile.loop r next nfa = result) :
  ∀ i, nfa.nodes.size ≤ i → (_ : i < result.val.nodes.size) →
  (∀ c, result.val[i].charStep c ⊆ {next} ∪ NewNodesRange eq) ∧
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
    intro c
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
    have size₁ : nfa₁.val.nodes.size < nfa'.val.nodes.size :=
      Nat.lt_of_le_of_lt nfa₂.property size₂

    cases Nat.lt_or_ge i nfa₁.val.nodes.size with
    | inl lt =>
      have ih₁ := ih₁ eq₁.symm i h₁ lt
      have : nfa'.val[i] = nfa₁.val[i] := by
        simp [eq₅]
        rw [NFA.get_lt_addNode (Nat.lt_of_lt_of_le lt nfa₂.property)]
        rw [get_lt eq₃.symm lt]
      rw [this]
      have : {next} ∪ NewNodesRange eq₁.symm ⊆
        {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa'.val.nodes.size} := by
        apply Set.insert_subset_insert
        apply Set.setOf_subset_setOf.mpr
        intro i h
        exact ⟨h.left, lt_trans h.right size₁⟩
      exact ⟨fun c => le_trans (ih₁.left c) this, le_trans ih₁.right this⟩
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
          exact ⟨le_trans nfa₁.property h.left, lt_trans h.right size₂⟩
        exact ⟨fun c => le_trans (ih₂.left c) this, le_trans ih₂.right this⟩
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
          exact .inr ⟨le_trans nfa₁.property h.left, lt_trans h.right size₂⟩
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq i h₁ h₂
    simp [NewNodesRange, eq]

    have size : i < nfa₁.val.nodes.size := by
      simp [eq] at h₂
      exact h₂

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
        exact ⟨h.left, Nat.lt_of_lt_of_le h.right nfa₁.property⟩
      exact ⟨fun c => le_trans (ih₂.left c) this, le_trans ih₂.right this⟩
    | inr ge =>
      have ih₁ := ih₁ eq₁.symm i ge size
      have : {nfa₂.val.start.val} ∪ NewNodesRange eq₁.symm ⊆
        {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa₁.val.nodes.size} := by
        apply Set.union_subset
        . simp
          have h := start_in_NewNodesRange eq₂.symm
          exact .inr ⟨h.left, Nat.lt_of_lt_of_le h.right nfa₁.property⟩
        . simp [Set.subset_def]
          intro i h
          exact .inr ⟨le_trans nfa₂.property h.left, h.right⟩
      exact ⟨fun c => le_trans (ih₁.left c) this, le_trans ih₁.right this⟩
  | star r ih =>
    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ eq₂ eq₃ eq₄ eq₅ eq i h₁ h₂
    simp [NewNodesRange, eq]

    have eqs : start.val = nfa.nodes.size := by
      simp [eq₂]
      rw [eq₁]
      simp [NFA.addNode]
    have size : i < nfa'''.nodes.size := by
      simp [eq] at h₂
      exact h₂
    have eqsize : nfa''.val.nodes.size = nfa'''.nodes.size := by
      simp [eq₅, eq₄]
    have size'' : i < nfa''.val.nodes.size := eqsize ▸ size

    cases Nat.lt_or_ge i nfa'.val.nodes.size with
    | inl lt =>
      simp [eq₁, NFA.addNode] at lt
      have h := Nat.eq_of_ge_of_lt h₁ lt
      have : nfa'''[i] = .split nfa''.val.start next := by
        have : i = start := by
          rw [h, eqs]
        simp [this, eq₅, NFA.eq_get, eq₄]
      simp [this, Node.charStep, Node.εStep]
      apply Set.insert_subset
      . have h := start_in_NewNodesRange eq₃.symm
        simp
        exact .inr ⟨le_trans nfa'.property h.left, eqsize ▸ nfa''.val.start.isLt⟩
      . simp
    | inr ge =>
      have ih := ih eq₃.symm i ge size''
      have : nfa'''[i] = nfa''.val[i] := by
        simp [eq₅, NFA.eq_get, eq₄]
        apply Array.get_set_ne
        rw [eqs]
        apply Nat.ne_of_lt
        have : nfa.nodes.size + 1 ≤ i := by
          simp [eq₁, NFA.addNode] at ge
          exact ge
        exact this
      rw [this]
      have : {start.val} ∪ NewNodesRange eq₃.symm ⊆
        {next} ∪ {i | nfa.nodes.size ≤ i ∧ i < nfa'''.nodes.size} := by
        apply Set.union_subset
        . simp
          have : start.val < nfa'''.nodes.size :=
            calc start.val
              _ < nfa'.val.nodes.size := start.isLt
              _ ≤ nfa''.val.nodes.size := nfa''.property
              _ = nfa'''.nodes.size := eqsize
          exact .inr ⟨by simp [eqs], this⟩
        . simp [Set.subset_def]
          intro i h
          exact .inr ⟨le_trans nfa'.property h.left, eqsize ▸ h.right⟩
      exact ⟨fun c => le_trans (ih.left c) this, le_trans ih.right this⟩

theorem compile.loop.lt_size (eq : compile.loop r next nfa = result) :
  nfa.nodes.size < result.val.nodes.size := by
  induction r generalizing next nfa with
  | empty =>
    apply compile.loop.empty eq
    intro eq
    simp [eq, NFA.addNode]
  | epsilon =>
    apply compile.loop.epsilon eq
    intro eq
    simp [eq, NFA.addNode]
  | char c' =>
    apply compile.loop.char eq
    intro eq
    simp [eq, NFA.addNode]
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ nfa' property eq₁ _ eq₃ _ eq₅ eq
    simp [eq, eq₅, NFA.addNode]
    calc nfa.nodes.size
      _ < nfa₁.val.nodes.size := ih₁ eq₁.symm
      _ < nfa₂.val.nodes.size := ih₂ eq₃.symm
      _ < _ := Nat.lt_succ_self _
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    simp [eq]
    calc nfa.nodes.size
      _ < nfa₂.val.nodes.size := ih₂ eq₂.symm
      _ < nfa₁.val.nodes.size := ih₁ eq₁.symm
  | star r _ =>
    apply compile.loop.star eq
    intro placeholder loopStart compiled nodes patched isLt isLt' property'
      eq₁ _ _ eq₄ eq₅ eq'
    calc nfa.nodes.size
      _ < placeholder.val.nodes.size := by simp [eq₁, NFA.addNode]
      _ ≤ compiled.val.nodes.size := compiled.property
      _ = _ := by
        rw [eq']
        simp [eq₅, eq₄]

theorem compile.loop.star.loopStartNode (eq : compile.loop (.star r) next nfa = result) :
  ∃ rStart ∈ { i | nfa.nodes.size + 1 ≤ i ∧ i < result.val.nodes.size },
  result.val[nfa.nodes.size]'(compile.loop.lt_size eq) = .split rStart next := by
  apply compile.loop.star eq
  intro placeholder loopStart compiled nodes patched isLt isLt' property'
    eq₁ eq₂ eq₃ eq₄ eq₅ eq'
  exists compiled.val.start.val
  have : nfa.nodes.size = (Fin.mk loopStart.val isLt).val := by
    simp [eq₂]
    rw [eq₁]
    simp [NFA.addNode]
  simp [this, eq', eq₅, NFA.eq_get, eq₄]
  calc loopStart.val + 1
    _ ≤ placeholder.val.nodes.size := loopStart.isLt
    _ ≤ _ := by
      have startRange := compile.loop.start_in_NewNodesRange eq₃.symm
      simp [NewNodesRange] at startRange
      exact startRange

@[simp]
theorem compile.loop.star.charStep_loopStartNode {c} (eq : compile.loop (.star r) next nfa = result) :
  (result.val[nfa.nodes.size]'(compile.loop.lt_size eq)).charStep c = ∅ := by
  let ⟨_, _, eq⟩ := compile.loop.star.loopStartNode eq
  simp [eq, Node.charStep]

end NFA

namespace NFAa

theorem pushRegex_get_lt (eq : pushRegex nfa next r = result) (i : Nat) (h : i < nfa.nodes.size) :
  result.val[i]'(Nat.lt_trans h result.property) = nfa[i] := by
  induction r generalizing next nfa with
  | empty | epsilon | char =>
    try apply pushRegex.empty eq
    try apply pushRegex.epsilon eq
    try apply pushRegex.char eq
    intro eq
    subst eq
    apply pushNode_get_lt i h
  | alternate r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.alternate eq
    intro nfa₁ start₁ nfa₂ start₂ _ nfa' property eq₁ _ eq₃ _ eq₅ eq

    have h₁ : i < nfa₁.val.nodes.size := Nat.lt_trans h nfa₁.property
    have h₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h₁ nfa₂.property

    simp [eq, eq₅, pushNode_get_lt _ h₂]
    simp [ih₂ eq₃.symm h₁]
    simp [ih₁ eq₁.symm h]
  | concat r₁ r₂ ih₁ ih₂ =>
    apply pushRegex.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq

    have h₂ : i < nfa₂.val.nodes.size := Nat.lt_trans h nfa₂.property

    simp [eq, ih₁ eq₁.symm h₂, ih₂ eq₂.symm h]
  | star r ih =>
    apply pushRegex.star eq
    intro placeholder compiled patched nfa' isLt inBounds property
      eq₁ eq₂ eq₃ eq₄ eq

    have ih := ih eq₂.symm (Nat.lt_trans h placeholder.property)

    conv =>
      lhs
      simp [eq, eq₄, get_eq_nodes_get, eq₃]

    have : i < compiled.val.nodes.size :=
      calc
        _ < _ := h
        _ < _ := placeholder.property
        _ < _ := compiled.property
    rw [Array.get_set (hj := this)]

    have : nfa.nodes.size ≠ i := Nat.ne_of_gt h
    simp [this, ←get_eq_nodes_get, ih, eq₁, pushNode_get_lt _ h]

end NFAa
