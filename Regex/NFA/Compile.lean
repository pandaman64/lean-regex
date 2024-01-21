import Regex.Lemmas
import Regex.Regex
import Regex.NFA.Basic

import Std.Data.Array.Lemmas

namespace NFAa

-- TODO: remove once migration is complete
open NFA

def pushNode (nfa : NFAa) (node : NFA.Node) (inBounds : node.inBounds (nfa.nodes.size + 1)) :
  { nfa' : NFAa // nfa.nodes.size < nfa'.nodes.size } :=
  let start := nfa.nodes.size
  let nodes := nfa.nodes.push node
  have inBounds := by
    intro i
    simp
    rw [Array.get_push]
    split
    case inl h =>
      have := nfa.inBounds ⟨i.val, h⟩
      apply Node.inBounds_of_inBounds_of_le this (Nat.le_succ _)
    case inr => exact inBounds
  let nfa' : NFAa := ⟨nodes, ⟨start, by simp⟩, inBounds⟩

  ⟨nfa', by simp⟩

@[simp]
theorem pushNode_size {nfa : NFAa} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)} :
  (nfa.pushNode node inBounds).val.nodes.size = nfa.nodes.size + 1 := by
  simp [pushNode]

theorem pushNode_get_lt {nfa : NFAa} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)}
  (i : Nat) (h : i < nfa.nodes.size) :
  (nfa.pushNode node inBounds).val[i]'(Nat.lt_trans h (nfa.pushNode node inBounds).property) = nfa[i] := by
  simp [pushNode, get_eq_nodes_get]
  rw [Array.get_push_lt]

@[simp]
theorem pushNode_get_eq {nfa : NFAa} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)} :
  (nfa.pushNode node inBounds).val[nfa.nodes.size] = node := by
  simp [pushNode, get_eq_nodes_get]

theorem pushNode_get {nfa : NFAa} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)}
  (i : Nat) (h : i < (nfa.pushNode node inBounds).val.nodes.size) :
  (nfa.pushNode node inBounds).val[i]'h = if h' : i < nfa.nodes.size then nfa[i]'h' else node := by
  simp at h
  cases Nat.lt_or_eq_of_le (Nat.le_of_succ_le_succ h) with
  | inl lt => simp [lt, pushNode_get_lt _ lt]
  | inr eq => simp [eq]

@[simp]
theorem pushNode_start_eq {nfa : NFAa} {node : Node} {inBounds : node.inBounds (nfa.nodes.size + 1)} :
  (nfa.pushNode node inBounds).val.start.val = nfa.nodes.size := rfl

/--
  Compile a Regex and append the resulting nodes to the NFA. The nodes will transition to `next` on match.
-/
def pushRegex (nfa : NFAa) (next : Fin nfa.nodes.size) :
  Regex → { nfa' : NFAa // nfa.nodes.size < nfa'.nodes.size }
  | .empty => nfa.pushNode .fail rfl
  | .epsilon => nfa.pushNode (.epsilon next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))
  | .char c => nfa.pushNode (.char c next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _))
  | .alternate r₁ r₂ =>
    -- TODO: it feels better to compile r₂ first to align with concat
    let nfa₁ := nfa.pushRegex next r₁
    let start₁ := nfa₁.val.start
    let nfa₂ := nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ r₂
    let start₂ := nfa₂.val.start

    let split := Node.split start₁ start₂
    have inBounds : split.inBounds (nfa₂.val.nodes.size + 1) := by
      have lt₁ : start₁ < nfa₂.val.nodes.size + 1 :=
        calc
          _ < _ := start₁.isLt
          _ < _ := nfa₂.property
          _ < _ := Nat.lt_succ_self _
      have lt₂ : start₂ < nfa₂.val.nodes.size + 1 := Nat.lt_trans start₂.isLt (Nat.lt_succ_self _)
      simp [lt₁, lt₂]

    let nfa' := nfa₂.val.pushNode split inBounds
    have property : nfa.nodes.size < nfa'.val.nodes.size :=
      calc
        _ < _ := nfa₁.property
        _ < _ := nfa₂.property
        _ < _ := nfa'.property

    ⟨nfa', property⟩
  | .concat r₁ r₂ =>
    let nfa₂ := nfa.pushRegex next r₂
    let nfa₁ := nfa₂.val.pushRegex nfa₂.val.start r₁

    ⟨nfa₁, Nat.lt_trans nfa₂.property nfa₁.property⟩
  | .star r =>
    -- We need to generate a placeholder node first. We use `fail` for it because
    -- 1. We'll use the fact that `fail` is a minimal element when strengthening induction hypotheis;
    -- 2. We want to make sure `done` does not appear except at the first node.
    -- 3. variants without data are represented as a boxed integer so there is one less allocation.
    let placeholder := nfa.pushNode .fail rfl
    let loopStart := placeholder.val.start
    -- FIXME: generated code keeps `placeholder` alive, copying the array. Why?
    let compiled := placeholder.val.pushRegex loopStart r

    -- Patch the placeholder node
    have isLt : loopStart.val < compiled.val.nodes.size :=
      calc
        _ < _ := loopStart.isLt
        _ < _ := compiled.property
    let loopStart := ⟨loopStart.val, isLt⟩

    let split := Node.split compiled.val.start next
    let patched := compiled.val.nodes.set loopStart split
    have inBounds := by
      -- Somehow putting the type directly on `inBounds` causes an infinite loop
      show ∀ i : Fin patched.size, patched[i].inBounds patched.size
      -- FIXME: I don't know how to unfold only `patched`
      show ∀ i : Fin (compiled.val.nodes.set loopStart split).size, (compiled.val.nodes.set loopStart split)[i].inBounds (compiled.val.nodes.set loopStart split).size
      intro i
      have hj : i < compiled.val.nodes.size := by
        suffices i.val < (compiled.val.nodes.set loopStart split).size by
          -- Bare simp expands `let` declarations
          simp (config := {zeta := false}) at this
          exact this
        exact i.isLt
      rw [getElem_fin, Array.get_set (hj := hj)]
      split
      case inl =>
        have lt₁ : compiled.val.start < compiled.val.nodes.size := compiled.val.start.isLt
        have lt₂ : next < compiled.val.nodes.size :=
          calc
            _ < _ := next.isLt
            _ < _ := placeholder.property
            _ < _ := compiled.property
        simp [lt₁, lt₂]
      case inr neq =>
        have := compiled.val.inBounds ⟨i, hj⟩
        simp (config := {zeta := false}) at this
        simp (config := {zeta := false})
        simp [this]

    let nfa' := ⟨patched, loopStart.cast (by rw [Array.size_set]), inBounds⟩
    have property :=
      calc
        _ < _ := placeholder.property
        _ < _ := compiled.property
        _ = nfa'.nodes.size := by simp

    ⟨nfa', property⟩

-- TODO: push .*? for search
def compile (r : Regex) : NFAa := done.pushRegex ⟨0, by decide⟩ r

-- Useful lemmas about the compilation
theorem pushRegex.empty (eq : pushRegex nfa next .empty = result)
  {motive : result = nfa.pushNode .fail rfl → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

theorem pushRegex.epsilon (eq : pushRegex nfa next .epsilon = result)
  {motive : result = nfa.pushNode (.epsilon next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _)) → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

theorem pushRegex.char (eq : pushRegex nfa next (.char c) = result)
  {motive : result = nfa.pushNode (.char c next) (by simp [Node.inBounds]; exact Nat.lt_trans next.isLt (Nat.lt_succ_self _)) → P} : P := by
  simp [pushRegex] at eq
  exact motive eq.symm

theorem pushRegex.alternate (eq : pushRegex nfa next (Regex.alternate r₁ r₂) = result)
  {motive : ∀ nfa₁ start₁ nfa₂ start₂ inBounds nfa' property,
    nfa₁ = nfa.pushRegex next r₁ →
    start₁ = nfa₁.val.start →
    nfa₂ = nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ r₂ →
    start₂ = nfa₂.val.start →
    nfa' = nfa₂.val.pushNode (.split start₁ start₂) inBounds →
    result = ⟨nfa', property⟩ →
    P
  } : P := by
  let nfa₁ := nfa.pushRegex next r₁
  let start₁ := nfa₁.val.start
  let nfa₂ := nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ r₂
  let start₂ := nfa₂.val.start

  let split := Node.split start₁ start₂
  have inBounds : split.inBounds (nfa₂.val.nodes.size + 1) := by
    have lt₁ : start₁ < nfa₂.val.nodes.size + 1 :=
      calc
        _ < _ := start₁.isLt
        _ < _ := nfa₂.property
        _ < _ := Nat.lt_succ_self _
    have lt₂ : start₂ < nfa₂.val.nodes.size + 1 := Nat.lt_trans start₂.isLt (Nat.lt_succ_self _)
    simp [lt₁, lt₂]

  let nfa' := nfa₂.val.pushNode split inBounds
  have property : nfa.nodes.size < nfa'.val.nodes.size :=
    calc
      _ < _ := nfa₁.property
      _ < _ := nfa₂.property
      _ < _ := nfa'.property

  exact motive nfa₁ start₁ nfa₂ start₂ inBounds nfa' property rfl rfl rfl rfl rfl eq.symm

theorem pushRegex.concat (eq : pushRegex nfa next (Regex.concat r₁ r₂) = result)
  {motive : ∀ nfa₂ nfa₁ property,
    nfa₂ = nfa.pushRegex next r₂ →
    nfa₁ = nfa₂.val.pushRegex nfa₂.val.start r₁ →
    result = ⟨nfa₁, property⟩ →
    P
  } : P := by
  let nfa₂ := nfa.pushRegex next r₂
  let nfa₁ := nfa₂.val.pushRegex nfa₂.val.start r₁

  have property : nfa.nodes.size < nfa₁.val.nodes.size :=
    calc
      _ < _ := nfa₂.property
      _ < _ := nfa₁.property

  exact motive nfa₂ nfa₁ property rfl rfl eq.symm

theorem pushRegex.star (eq : pushRegex nfa next (Regex.star r) = result)
  {motive : ∀ placeholder compiled patched nfa' isLt inBounds property,
    placeholder = nfa.pushNode .fail rfl →
    compiled = placeholder.val.pushRegex ⟨nfa.nodes.size, placeholder.property⟩ r →
    patched = compiled.val.nodes.set
      ⟨nfa.nodes.size, Nat.lt_trans placeholder.property compiled.property⟩
      (Node.split compiled.val.start next) →
    nfa' = ⟨patched, ⟨nfa.nodes.size, isLt⟩, inBounds⟩ →
    result = ⟨nfa', property⟩ →
    P
  } : P := by
  let placeholder := nfa.pushNode .fail rfl
  let compiled := placeholder.val.pushRegex ⟨nfa.nodes.size, placeholder.property⟩ r

  -- Patch the placeholder node
  let loopStart : Fin _ := ⟨nfa.nodes.size, Nat.lt_trans placeholder.property compiled.property⟩
  let split := Node.split compiled.val.start next
  let patched := compiled.val.nodes.set loopStart split
  have inBounds := by
    -- Somehow putting the type directly on `inBounds` causes an infinite loop
    show ∀ i : Fin patched.size, patched[i].inBounds patched.size
    -- FIXME: I don't know how to unfold only `patched`
    show ∀ i : Fin (compiled.val.nodes.set loopStart split).size, (compiled.val.nodes.set loopStart split)[i].inBounds (compiled.val.nodes.set loopStart split).size
    intro i
    have hj : i < compiled.val.nodes.size := by
      suffices i.val < (compiled.val.nodes.set loopStart split).size by
        -- Bare simp expands `let` declarations
        simp (config := {zeta := false}) at this
        exact this
      exact i.isLt
    rw [getElem_fin, Array.get_set (hj := hj)]
    split
    case inl =>
      have lt₁ : compiled.val.start < compiled.val.nodes.size := compiled.val.start.isLt
      have lt₂ : next < compiled.val.nodes.size :=
        calc
          _ < _ := next.isLt
          _ < _ := placeholder.property
          _ < _ := compiled.property
      simp [lt₁, lt₂]
    case inr neq =>
      have := compiled.val.inBounds ⟨i, hj⟩
      simp (config := {zeta := false}) at this
      simp (config := {zeta := false})
      simp [this]

  have isLt : nfa.nodes.size < patched.size :=
    calc
      _ < _ := placeholder.property
      _ < _ := compiled.property
      _ = _ := by simp
  let nfa' : NFAa := ⟨patched, ⟨nfa.nodes.size, isLt⟩, inBounds⟩
  have property :=
    calc
      _ < _ := placeholder.property
      _ < _ := compiled.property
      _ = nfa'.nodes.size := by simp

  exact motive placeholder compiled patched nfa' isLt inBounds property rfl rfl rfl rfl eq.symm

end NFAa

namespace NFA

def NFA.addNode (nfa : NFA) (node : Node) :
  { nfa' : NFA // nfa.nodes.size ≤ nfa'.nodes.size } :=
  have isLt : nfa.nodes.size < (nfa.nodes.push node).size := by
    simp [Array.size_push]
  let start := nfa.nodes.size
  let nfa' : NFA := ⟨nfa.nodes.push node, ⟨start, isLt⟩⟩

  have property : nfa.nodes.size ≤ nfa'.nodes.size := by
    simp
    exact Nat.le_succ _

  ⟨nfa', property⟩

@[simp]
theorem NFA.size_addNode {nfa : NFA} {node : Node} :
  (nfa.addNode node).val.nodes.size = nfa.nodes.size + 1 := by
  simp [NFA.addNode]

theorem NFA.lt_size_addNode {nfa : NFA} {node : Node} :
  nfa.nodes.size < (nfa.addNode node).val.nodes.size := (nfa.addNode node).val.start.isLt

theorem NFA.get_lt_addNode {nfa : NFA} {node : Node} (h : i < nfa.nodes.size) :
  (nfa.addNode node).val[i]'(Nat.lt_trans h lt_size_addNode) = nfa[i] :=
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

theorem NFA.start_addNode {nfa : NFA} {node : Node} {result : { nfa' : NFA // nfa.nodes.size ≤ nfa'.nodes.size }}
  (eq : nfa.addNode node = result) :
  result.val.start.val = nfa.nodes.size := by
  rw [←eq]
  simp [NFA.addNode]

@[export lean_regex_nfa_compile_regex]
def compile (r : Regex) : NFA :=
  let result := loop r 0 init
  result.val
where
  init : NFA := ⟨#[.done], ⟨0, Nat.zero_lt_succ _⟩⟩
  /--
    The main loop of the compilation.

    It compiles the given regex into nodes that transitions to `next` on match.
    Returned NFA contains the compiled nodes at the end and starts at the node
    corresponding to the given regex.
  -/
  loop (r : Regex) (next : Nat) (nfa : NFA) : { nfa' // nfa.nodes.size ≤ nfa'.nodes.size } := match r with
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

    have property : nfa.nodes.size ≤ nfa'.val.nodes.size :=
      calc nfa.nodes.size
        _ ≤ nfa₁.val.nodes.size := nfa₁.property
        _ ≤ nfa₂.val.nodes.size := nfa₂.property
        _ ≤ nfa'.val.nodes.size := nfa'.property

    ⟨nfa', property⟩
  | .concat r₁ r₂ =>
    let nfa₂ := loop r₂ next nfa
    let nfa₁ := loop r₁ nfa₂.val.start nfa₂

    have property : nfa.nodes.size ≤ nfa₁.val.nodes.size :=
      calc nfa.nodes.size
        _ ≤ nfa₂.val.nodes.size := nfa₂.property
        _ ≤ nfa₁.val.nodes.size := nfa₁.property

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

    have property : nfa.nodes.size ≤ nfa''.val.nodes.size :=
      calc nfa.nodes.size
        _ ≤ nfa'.val.nodes.size := nfa'.property
        _ ≤ nfa''.val.nodes.size := nfa''.property
    have isLt : start.val < nfa''.val.nodes.size :=
      Nat.lt_of_lt_of_le nfa'.val.start.isLt nfa''.property

    -- Patch the placeholder node
    let target := nfa''.val.start
    let nodes''' := nfa''.val.nodes.set ⟨start.val, isLt⟩ (.split target next)

    -- TODO: maybe I should have used Fin.cast
    have eq_size : nodes'''.size = nfa''.val.nodes.size := by simp
    have isLt' : start.val < nodes'''.size := eq_size ▸ isLt
    let nfa''' := ⟨nodes''', ⟨start.val, isLt'⟩⟩

    have property' : nfa.nodes.size ≤ nfa'''.nodes.size := by
      simp
      exact property

    ⟨nfa''', property'⟩

-- Useful lemmas about the compilation
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

  have property : nfa.nodes.size ≤ nfa'.val.nodes.size :=
    calc nfa.nodes.size
      _ ≤ nfa₁.val.nodes.size := nfa₁.property
      _ ≤ nfa₂.val.nodes.size := nfa₂.property
      _ ≤ nfa'.val.nodes.size := nfa'.property

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

  have property : nfa.nodes.size ≤ nfa₁.val.nodes.size :=
    calc nfa.nodes.size
      _ ≤ nfa₂.val.nodes.size := nfa₂.property
      _ ≤ nfa₁.val.nodes.size := nfa₁.property

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

  have property : nfa.nodes.size ≤ nfa''.val.nodes.size :=
    calc nfa.nodes.size
      _ ≤ nfa'.val.nodes.size := nfa'.property
      _ ≤ nfa''.val.nodes.size := nfa''.property
  have isLt : start.val < nfa''.val.nodes.size :=
    Nat.lt_of_lt_of_le nfa'.val.start.isLt nfa''.property

  -- Patch the placeholder node
  let nodes''' := nfa''.val.nodes.set ⟨start.val, isLt⟩ (.split nfa''.val.start next)

  have eq_size : nodes'''.size = nfa''.val.nodes.size := by simp
  have isLt' : start.val < nodes'''.size := eq_size ▸ isLt
  let nfa''' : NFA := ⟨nodes''', ⟨start.val, isLt'⟩⟩

  have property' : nfa.nodes.size ≤ nfa'''.nodes.size := by
    simp
    exact property

  have : result = ⟨nfa''', property'⟩ := by
    simp [eq.symm, compile.loop]
  exact motive nfa' start nfa'' nodes''' nfa''' isLt isLt' property' rfl rfl rfl rfl rfl this

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
    have h' : next < nfa.nodes.size + 1 := Nat.lt_trans h₁ (Nat.lt_succ_self _)

    cases Nat.lt_or_ge i nfa.nodes.size with
    | inl lt =>
      simp [NFA.get_lt_addNode lt]
      exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) (Nat.le_succ _)
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
      have ih₁ := ih₁ eq₁.symm h₁ h₂
      have ih₂ := ih₂ eq₃.symm (Nat.lt_of_lt_of_le h₁ nfa₁.property) ih₁
      exact Node.inBounds_of_inBounds_of_le (ih₂ ⟨i, h⟩) (Nat.le_succ _)

    cases Nat.lt_or_ge i nfa₂.val.nodes.size with
    | inl lt => exact ih lt
    | inr ge =>
      let lt := i.isLt
      simp only [eq, eq₅, NFA.addNode, Array.size_push] at lt
      have : i = nfa₂.val.nodes.size := Nat.eq_of_ge_of_lt ge lt
      simp [eq, eq₅, this]
      apply Node.inBounds.split
      . exact Nat.lt_trans start₁.isLt (Nat.lt_of_le_of_lt nfa₂.property (Nat.lt_succ_self _))
      . exact Nat.lt_trans start₂.isLt (Nat.lt_succ_self _)
  | concat r₁ r₂ ih₁ ih₂ =>
    apply compile.loop.concat eq
    intro nfa₂ nfa₁ property eq₂ eq₁ eq
    simp [eq]
    apply ih₁ eq₁.symm nfa₂.val.start.isLt
    apply ih₂ eq₂.symm h₁ h₂
  | star r ih =>
    apply compile.loop.star eq
    intro nfa' start nfa'' nodes''' nfa''' isLt isLt' property'
      eq₁ _ eq₃ eq₄ eq₅ eq i

    have eqsize : result.val.nodes.size = nfa''.val.nodes.size := by
      simp [eq, eq₅, eq₄]
    have h' : i < nfa''.val.nodes.size :=
      calc
        i < result.val.nodes.size := i.isLt
        _ = _ := eqsize
    have inBounds' : nfa'.val.inBounds := by
      simp [eq₁]
      intro i
      cases Nat.lt_or_ge i nfa.nodes.size with
      | inl lt =>
        simp [NFA.get_lt_addNode lt]
        exact Node.inBounds_of_inBounds_of_le (h₂ ⟨i, lt⟩) (Nat.le_succ _)
      | inr ge =>
        let lt := i.isLt
        simp only [NFA.addNode, Array.size_push] at lt
        have : i = nfa.nodes.size := Nat.eq_of_ge_of_lt ge lt
        simp [this]
    have ih := ih eq₃.symm start.isLt inBounds'

    simp [eq, eq₅, NFA.eq_get, eq₄, Array.get_set, h']
    split
    . apply Node.inBounds.split
      . exact nfa''.val.start.isLt
      . exact Nat.lt_of_lt_of_le h₁ (Nat.le_trans nfa'.property nfa''.property)
    . exact ih (i.cast eqsize)

theorem compile.init.inBounds : compile.init.inBounds := by
  intro i
  simp [NFA.eq_get, init]
  match i with
  | ⟨0, _⟩ =>
    show Node.done.inBounds 1
    simp [Node.inBounds]
  | ⟨i + 1, isLt⟩ =>
    simp [init] at isLt
    contradiction

theorem compile.inBounds (eq : compile r = result) : result.inBounds := by
  simp [eq.symm, compile]
  exact compile.loop.inBounds rfl (by decide) compile.init.inBounds

end NFA
