import Regex.NFA.Basic
import Regex.NFA.VM.NodeSet

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

-- TODO: check if the modifications don't cause copying
def εClosureTR (nfa : NFA) (visited : NodeSet nfa.nodes.size) (stack : Array (Fin nfa.nodes.size)) :
  NodeSet nfa.nodes.size :=
  if hemp : stack.isEmpty then
    visited
  else
    let i := stack.back' hemp
    let stack' := stack.pop
    have : stack'.size < stack.size := Array.lt_size_of_pop_of_not_empty _ hemp
    if hvis : visited.get i then
      εClosureTR nfa visited stack'
    else
      let visited' := visited.set i
      have : visited'.count_unset < visited.count_unset := visited.lt_count_unset i.isLt hvis
      have inBounds' := nfa.inBounds i
      let stack'' :=
        match hn : nfa.nodes[i.val] with
        | .epsilon next =>
          have h : next < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [Node.inBounds] at inBounds'
            exact inBounds'

          stack'.push ⟨next, h⟩
        | .split next₁ next₂ =>
          have h₁ : next₁ < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [Node.inBounds] at inBounds'
            exact inBounds'.left
          have h₂ : next₂ < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [Node.inBounds] at inBounds'
            exact inBounds'.right

          (stack'.push ⟨next₁, h₁⟩).push ⟨next₂, h₂⟩
        | _ => stack'
      εClosureTR nfa visited' stack''
termination_by _ => (visited.count_unset, stack.size)

def charStepTR (nfa : NFA) (c : Char) (init : NodeSet nfa.nodes.size) :
  NodeSet nfa.nodes.size := go nfa c init .empty 0 (Nat.zero_le _)
where
  go (nfa : NFA) (c : Char) (init : NodeSet nfa.nodes.size)
    (accum : NodeSet nfa.nodes.size) (i : Nat) (hle : i ≤ nfa.nodes.size) :
    NodeSet nfa.nodes.size :=
    if h : i = nfa.nodes.size then
      accum
    else
      have hlt : i < nfa.nodes.size := Nat.lt_of_le_of_ne hle h
      let accum := if init.get ⟨i, hlt⟩ then
        match hn : nfa.nodes[i] with
        | .char c' next =>
          if c = c' then
            have : next < nfa.nodes.size := by
              have := nfa.inBounds ⟨i, hlt⟩
              simp [hn, Node.inBounds] at this
              exact this
            -- TODO: reuse visited and stack
            accum.merge (εClosureTR nfa .empty #[⟨next, this⟩])
          else
            accum
        | _ => accum
      else accum
      go nfa c init accum (i + 1) hlt
termination_by go _ => nfa.nodes.size - i

end NFA.VM

open NFA.VM

@[export lean_regex_nfa_match]
def NFA.match (nfa : NFA) (s : String) : Bool :=
  let ns := εClosureTR nfa .empty #[nfa.start]
  let ns := go nfa s.iter ns
  -- This assumes that the first node is the accepting node
  ns.get ⟨0, nfa.zero_lt_size⟩
where
  go (nfa : NFA) (iter : String.Iterator) (ns : NodeSet nfa.nodes.size) : NodeSet nfa.nodes.size :=
    if iter.atEnd then
      ns
    else
      -- Move if here to avoid confusing termination checker
      if ns.count_set = 0 then
        ns
      else
        let ns' := charStepTR nfa iter.curr ns
        go nfa iter.next ns'

def NFA.search_prefix (nfa : NFA) (s : String) : Option String.Iterator :=
  let ns := εClosureTR nfa .empty #[nfa.start]
  go s.iter ns .none
where
  go (it : String.Iterator) (ns : NodeSet nfa.nodes.size) (lastMatch : Option String.Iterator) :
    Option String.Iterator :=
    -- Prioritize the later match
    let lastMatch := if ns.get ⟨0, nfa.zero_lt_size⟩ then
      some it
    else
      lastMatch
    if it.atEnd then
      lastMatch
    else
      if ns.count_set = 0 then
        lastMatch
      else
        let ns' := charStepTR nfa it.curr ns
        go it.next ns' lastMatch
