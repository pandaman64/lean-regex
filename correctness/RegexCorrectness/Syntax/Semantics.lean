import Regex.Syntax.Ast
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (Iterator)
open Regex.Data (CaptureGroups Expr)

namespace Regex.Syntax.Parser.Ast

def groupCount (ast : Ast) : Nat :=
  match ast with
  | .empty | .epsilon | .anchor _ | .char _ | .classes _ | .perl _ | .dot => 0
  | .group e => e.groupCount + 1
  | .alternate e₁ e₂ => e₁.groupCount + e₂.groupCount
  | .concat e₁ e₂ => e₁.groupCount + e₂.groupCount
  | .repeat _ _ _ e => e.groupCount

inductive Captures : Nat → Iterator → Iterator → CaptureGroups → Ast → Prop where
  | epsilon {currentGroup it} (v : it.Valid) : Captures currentGroup it it .empty .epsilon
  | anchor {currentGroup it anchor} (v : it.Valid) (h : anchor.test it) : Captures currentGroup it it .empty (.anchor anchor)
  | char {currentGroup it l c r} (vf : it.ValidFor l (c :: r)) : Captures currentGroup it it.next .empty (.char c)
  | classes {currentGroup it l c r cs} (vf : it.ValidFor l (c :: r)) (h : c ∈ cs) : Captures currentGroup it it.next .empty (.classes cs)
  | perl {currentGroup it l c r cs} (vf : it.ValidFor l (c :: r)) (h : c ∈ cs) : Captures currentGroup it it.next .empty (.perl cs)
  | dot {currentGroup it l c r} (vf : it.ValidFor l (c :: r)) (h : c ≠ '\n') : Captures currentGroup it it.next .empty .dot
  | group {currentGroup it it' groups tag e} (cap : Captures (currentGroup + 1) it it' groups e) :
    Captures currentGroup it it' (.group tag it.pos it'.pos groups) (.group e)
  | alternateLeft {currentGroup it it' groups e₁ e₂} (cap : Captures currentGroup it it' groups e₁) :
    Captures currentGroup it it' groups (.alternate e₁ e₂)
  | alternateRight {currentGroup it it' groups e₁ e₂} (cap : Captures (currentGroup + e₁.groupCount) it it' groups e₂) :
    Captures currentGroup it it' groups (.alternate e₁ e₂)
  | concat {currentGroup it it' it'' groups₁ groups₂ e₁ e₂} (cap₁ : Captures currentGroup it it' groups₁ e₁) (cap₂ : Captures (currentGroup + e₁.groupCount) it' it'' groups₂ e₂) :
    Captures currentGroup it it'' (.concat groups₁ groups₂) (.concat e₁ e₂)
  | repeatEpsilon {currentGroup it max greedy e} (v : it.Valid) : Captures currentGroup it it .empty (.repeat 0 max greedy e)
  | repeatMoreLimited {currentGroup it it' it'' groups groups' min max greedy e}
    (cap₁ : Captures currentGroup it it' groups e) (cap₂ : Captures currentGroup it' it'' groups' (.repeat (Nat.pred min) (.some max) greedy e)) :
    Captures currentGroup it it'' (.concat groups groups') (.repeat min (.some (max + 1)) greedy e)
  | repeatMoreUnlimited {currentGroup it it' it'' groups groups' min greedy e}
    (cap₁ : Captures currentGroup it it' groups e) (cap₂ : Captures currentGroup it' it'' groups' (.repeat (Nat.pred min) .none greedy e)) :
    Captures currentGroup it it'' (.concat groups groups') (.repeat min .none greedy e)

example {currentGroup it it' groups e min max greedy e'}
  (cap : Captures currentGroup it it' groups e) (eq : e = (.repeat min (.some max) greedy e')) (h : min > max) : False := by
  induction cap generalizing min max greedy e' with
  | epsilon | anchor | char | classes | perl | dot
  | group | alternateLeft | alternateRight | concat
  | repeatEpsilon | repeatMoreUnlimited => grind
  | @repeatMoreLimited currentGroup it it' it'' groups groups' min' max' greedy' e'' cap₁ cap₂ ih₁ ih₂ =>
    simp only [«repeat».injEq, Option.some.injEq] at eq
    simp only [←eq] at h
    match min' with
    | 0 => grind
    | min' + 1 => exact ih₂ rfl (by simpa using h)

proof_wanted captures_iff_captures {currentGroup it it' groups e} :
  Captures currentGroup it it' groups e ↔ Expr.Captures it it' groups (e.toRegexAux currentGroup).2

end Regex.Syntax.Parser.Ast
