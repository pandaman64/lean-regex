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
    let nfa₁ := loop r₁ next nfa₂

    have property : nfa ≤ nfa₁ :=
      calc nfa
        _ ≤ nfa₂.val := nfa₂.property
        _ ≤ nfa₁.val := nfa₁.property

    ⟨nfa₁, property⟩
  | .star r =>
    -- We need to generate a placeholder node first. We use `done` for it because variants
    -- without data are represented as a boxed integer so there is no allocation.
    -- TODO: check generated code
    let nfa' := nfa.addNode .done
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
#eval compile (Regex.alternate (Regex.char 'a') (Regex.star (Regex.concat (Regex.char 'a') (Regex.char 'b'))))
#eval compile (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))

end NFA
