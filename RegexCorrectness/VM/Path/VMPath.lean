import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (Span)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.NFA

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) : Span → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | init {l r i update} (cls : nfa.εClosure' ⟨l, [], r⟩ ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf ⟨l, [], r⟩  i update
  | more {i j k span c r' update₁ update₂} (prev : VMPath nfa wf span i update₁) (h : span.r = c :: r')
    (step : nfa.CharStep span.l span.m c r' i j) (cls : nfa.εClosure' span.next j k update₂) :
    VMPath nfa wf span.next k (update₁ ++ update₂)

end Regex.NFA

namespace Regex.VM

def SearchState'.Inv (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (next : SearchState' nfa) : Prop :=
  ∀ i ∈ next.states,
    ∃ span update,
      span.iterator = it ∧
      nfa.VMPath wf span i update ∧
      (WriteUpdate i → next.updates[i] = update)

end Regex.VM
