import RegexCorrectness.VM.EpsilonClosure.Path
import RegexCorrectness.VM.CharStep.Path

set_option autoImplicit false

open Regex.Data (Span)
open Regex (NFA)
open String (Pos)

namespace Regex.NFA

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) : Span → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | init {l r i update} (cls : nfa.εClosure' ⟨l, [], r⟩ ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf ⟨l, [], r⟩  i update
  | more {i j k span c r' update₁ update₂} (prev : VMPath nfa wf span i update₁) (h : span.r = c :: r')
    (step : nfa.CharStep span.l span.m c r' i j) (cls : nfa.εClosure' span.next j k update₂) :
    VMPath nfa wf span.next k (update₁ ++ update₂)

end Regex.NFA
