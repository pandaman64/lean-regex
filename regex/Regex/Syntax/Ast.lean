import Regex.Data.Anchor
import Regex.Data.Classes
import Regex.Data.Expr
import Regex.Unicode.CaseFold

set_option autoImplicit false

open Regex.Data (Anchor Class Classes PerlClass Expr)

namespace Regex.Syntax.Parser

inductive Ast : Type where
  | empty : Ast
  | epsilon : Ast
  | anchor : Anchor → Ast
  | char : Char → Ast
  | group : Ast → Ast
  | alternate : Ast → Ast → Ast
  | concat : Ast → Ast → Ast
  | repeat : Nat → Option Nat → Bool → Ast → Ast
  | classes : Classes → Ast
  | perl : PerlClass → Ast
  | dot : Ast
  | flags : (caseInsensitive : Bool) → Ast
deriving Inhabited, Repr, DecidableEq

def repeatConcat (e : Expr) (n : Nat) : Expr :=
  go e (n - 1)
where
  go (accum : Expr) : Nat → Expr
    | 0 => accum
    | n + 1 => go (.concat accum e) n

def applyRepetitions (min : Nat) (max : Option Nat) (greedy : Bool) (e : Expr) : Expr :=
  match min, max with
  | 0, .some 1 => if greedy then .alternate e .epsilon else .alternate .epsilon e
  | 0, .none => .star greedy e
  | 1, .none => .concat e (.star greedy e)
  | min, .none => .concat (repeatConcat e min) (.star greedy e)
  | 0, .some max =>
    if max == 0 then .epsilon
    else repeatConcat (.alternate e .epsilon) max
  | min, .some max =>
    if min == max then repeatConcat e min
    else
      let e' := if greedy then .alternate e .epsilon else .alternate .epsilon e
      .concat (repeatConcat e min) (repeatConcat e' (max - min))

def charToCaseInsensitive (c : Char) : Expr :=
  let (rep, equivChars) := Regex.Unicode.getCaseFoldEquivChars c
  if equivChars.size > 0 then
    .classes (equivChars.foldl (init := .atom (.single rep)) fun acc ch =>
      .union acc (.atom (.single ch)))
  else
    .char rep

structure ToRegexState where
  index : Nat
  caseInsensitive : Bool := false

def Ast.toRegexAux (state : ToRegexState) (ast : Ast) : ToRegexState × Expr :=
  match ast with
  | .empty => (state, .empty)
  | .epsilon => (state, .epsilon)
  | .anchor a => (state, .anchor a)
  | .char c =>
    if state.caseInsensitive then
      (state, charToCaseInsensitive c)
    else
      (state, .char c)
  | .group h =>
    let (state', r) := h.toRegexAux { state with index := state.index + 1 }
    ({ state' with caseInsensitive := state.caseInsensitive }, .group state.index r)
  | .alternate h₁ h₂ =>
    let (state₁, r₁) := h₁.toRegexAux state
    let (state₂, r₂) := h₂.toRegexAux state₁
    (state₂, .alternate r₁ r₂)
  | .concat h₁ h₂ =>
    let (state₁, r₁) := h₁.toRegexAux state
    let (state₂, r₂) := h₂.toRegexAux state₁
    (state₂, .concat r₁ r₂)
  | .repeat min max greedy h =>
    let (state', r) := h.toRegexAux state
    (state', applyRepetitions min max greedy r)
  | .classes cs => (state, .classes cs)
  | .perl pc => (state, .classes (Classes.atom (Class.perl pc)))
  | .dot => (state, .classes (.union (Classes.atom Class.beforeLineBreak) (Classes.atom Class.afterLineBreak)))
  | .flags ci => ({ state with caseInsensitive := ci }, .epsilon)

def Ast.toRegex (ast : Ast) : Expr := (ast.toRegexAux ⟨0, false⟩ ).2

end Regex.Syntax.Parser
