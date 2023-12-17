import Regex.Regex
import Regex.NFA.Basic

import Mathlib.Tactic.Common

namespace NFA

def addNode (nodes : Array Node) (node : Node) :
  (nodes' : { nodes' : Array Node // nodes.size < nodes'.size}) ×
  { i : Fin nodes'.val.size // i = nodes.size } :=
  have lt_size : nodes.size < (nodes.push node).size := by
    simp [Array.size_push]
  have isLt : nodes.size < (nodes.push node).size := by
    simp [Array.size_push]
  ⟨⟨nodes.push node, lt_size⟩, ⟨⟨nodes.size, isLt⟩, rfl⟩⟩

theorem addNode.get_lt {nodes : Array Node} {node : Node} {i : Nat} (h : i < nodes.size) :
  (addNode nodes node).1.val[i]'(Nat.lt_trans h (addNode nodes node).1.property) = nodes[i] := by
  simp [addNode]
  apply Array.get_push_lt

@[simp]
theorem addNode.get_node {nodes : Array Node} {node : Node} :
  (addNode nodes node).1.val[(addNode nodes node).2.val] = node := by
  show (addNode nodes node).1.val[(addNode nodes node).2.val.val] = node
  simp [addNode]

/--
  Thompson construction algorithm for converting the given regex to NFA.
-/
def compileRaw (r : Regex) :
  (nodes : Array Node) × Fin nodes.size :=
  let result := loop #[.done] 0 r
  ⟨result.1.val, result.2⟩
where
  /--
    The main loop of the compilation.

    It compiles the given regex into the given `nodes`. The compiled nodes transition to `next`
    if and only if the input matches. It returns the new `nodes` and the corresponding ID for the
    given regex in the array.
  -/
  loop (nodes : Array Node) (next : Nat) :
    Regex → (nodes' : { nodes' : Array Node // nodes.size < nodes'.size}) × Fin nodes'.val.size
  | .empty =>
    let ⟨nodes, start⟩ := addNode nodes .fail
    ⟨nodes, start.val⟩
  | .epsilon =>
    let ⟨nodes, start⟩ := addNode nodes (.epsilon next)
    ⟨nodes, start.val⟩
  | .char c =>
    let ⟨nodes, start⟩ := addNode nodes (.char c next)
    ⟨nodes, start.val⟩
  | .alternate r₁ r₂ =>
    let ⟨nodes₁, start₁⟩ := loop nodes next r₁
    let ⟨nodes₂, start₂⟩ := loop nodes₁ next r₂
    let ⟨nodes', start⟩ := addNode nodes₂ (.split start₁ start₂)

    have property : nodes.size < nodes'.val.size :=
      calc nodes.size
        _ < nodes₁.val.size := nodes₁.property
        _ < nodes₂.val.size := nodes₂.property
        _ < nodes'.val.size := nodes'.property

    ⟨⟨nodes', property⟩, start⟩
  | .concat r₁ r₂ =>
    let ⟨nodes₂, start₂⟩ := loop nodes next r₂
    let ⟨nodes₁, start₁⟩ := loop nodes₂ start₂ r₁

    have property : nodes.size < nodes₁.val.size :=
      calc nodes.size
        _ < nodes₂.val.size := nodes₂.property
        _ < nodes₁.val.size := nodes₁.property

    ⟨⟨nodes₁, property⟩, start₁⟩
  | .star r =>
    -- We need to generate a placeholder node first. We use `done` for it to save an allocation.
    -- TODO: check generated code
    let ⟨nodes', ⟨start, _⟩⟩ := addNode nodes .done
    let ⟨nodes'', target⟩ := loop nodes' start r

    have property : nodes.size < nodes''.val.size :=
      calc nodes.size
        _ < nodes'.val.size := nodes'.property
        _ < nodes''.val.size := nodes''.property
    have isLt : start.val < nodes''.val.size :=
      calc start.val
        _ < nodes'.val.size := start.isLt
        _ < nodes''.val.size := nodes''.property

    -- Patch the placeholder node
    let nodes''' := nodes''.val.set ⟨start.val, isLt⟩ (.split target next)

    have eq_size : nodes'''.size = nodes''.val.size := by simp
    have isLt : start.val < nodes'''.size := by
      rw [eq_size]
      exact isLt

    ⟨⟨nodes''', eq_size ▸ property⟩, ⟨start.val, isLt⟩⟩

def compileRaw.loop.get_lt {i : Nat} (h : i < nodes.size) :
  (loop nodes next r).1.val[i]'(Nat.lt_trans h (loop nodes next r).1.property) = nodes[i] := by
  -- have isLt := Nat.lt_trans h (loop nodes next r).1.property
  induction r generalizing nodes next with
  | empty | epsilon | char c => simp [loop]; apply addNode.get_lt
  | alternate r₁ r₂ ih₁ ih₂ =>
    let result₁ := loop nodes next r₁
    let result₂ := loop result₁.1 next r₂
    let result := addNode result₂.1 (.split result₁.2 result₂.2)

    have isLt₁ : i < result₁.1.val.size := Nat.lt_trans h result₁.1.property
    have isLt₂ : i < result₂.1.val.size := Nat.lt_trans isLt₁ result₂.1.property
    have isLt : i < result.1.val.size := Nat.lt_trans isLt₂ result.1.property

    show result.1.val[i] = nodes[i]

    calc result.1.val[i]
      _ = result₂.1.val[i] := addNode.get_lt isLt₂
      _ = result₁.1.val[i] := ih₂ isLt₁
      _ = nodes[i] := ih₁ h
  | concat r₁ r₂ ih₁ ih₂ =>
    let result₂ := loop nodes next r₂
    let result₁ := loop result₂.1 result₂.2 r₁

    have isLt₂ : i < result₂.1.val.size := Nat.lt_trans h result₂.1.property
    have isLt₁ : i < result₁.1.val.size := Nat.lt_trans isLt₂ result₁.1.property

    show result₁.1.val[i] = nodes[i]

    calc result₁.1.val[i]
      _ = result₂.1.val[i] := ih₁ isLt₂
      _ = nodes[i] := ih₂ h
  | star r ih =>
    let result := addNode nodes .done
    let result' := loop result.1 result.2 r

    have property : nodes.size < result'.1.val.size :=
      calc nodes.size
        _ < result.1.val.size := result.1.property
        _ < result'.1.val.size := result'.1.property
    have startIsLt : result.2.val.val < result'.1.val.size :=
      calc result.2.val.val
        _ < result.1.val.size := result.2.val.isLt
        _ < result'.1.val.size := result'.1.property

    let nodes' := result'.1.val.set ⟨result.2.val, startIsLt⟩ (.split result'.2 next)

    have eq_size : nodes'.size = result'.1.val.size := by simp

    have isLt : i < result.1.val.size := Nat.lt_trans h result.1.property
    have isLt' : i < result'.1.val.size := Nat.lt_trans isLt result'.1.property
    have isLt'' : i < nodes'.size := eq_size ▸ Nat.lt_trans h startIsLt

    show nodes'[i] = nodes[i]

    calc nodes'[i]
      _ = result'.1.val[i] := by
        rw [Array.get_set_ne]
        exact Nat.ne_of_gt (result.2.property.symm ▸ h)
      _ = result.1.val[i] := ih isLt
      _ = nodes[i] := addNode.get_lt h

def compile (r : Regex) : NFA :=
  let result := compileRaw r
  let nodes := result.1
  let start := result.2

  -- TODO: inBoundsはNatを受け取った方が証明が楽そう。nodesの内容を見ないで良いため
  ⟨nodes, start, sorry⟩

#eval compile (Regex.star (Regex.char 'a'))
#eval compile (Regex.alternate (Regex.char 'a') (Regex.star (Regex.concat (Regex.char 'a') (Regex.char 'b'))))
#eval compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))

end NFA
