import Regex.Data.Anchor
import Regex.Data.Classes
import Regex.Data.Expr

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

def Ast.toRegexAux (index : Nat) (ast : Ast) : Nat × Expr :=
  match ast with
  | .empty => (index, .empty)
  | .epsilon => (index, .epsilon)
  | .anchor a => (index, .anchor a)
  | .char c => (index, .char c)
  | .group h =>
    let (index', r) := h.toRegexAux (index + 1)
    (index', .group index r)
  | .alternate h₁ h₂ =>
    let (index₁, r₁) := h₁.toRegexAux index
    let (index₂, r₂) := h₂.toRegexAux index₁
    (index₂, .alternate r₁ r₂)
  | .concat h₁ h₂ =>
    let (index₁, r₁) := h₁.toRegexAux index
    let (index₂, r₂) := h₂.toRegexAux index₁
    (index₂, .concat r₁ r₂)
  | .repeat min max greedy h =>
    let (index', r) := h.toRegexAux index
    (index', applyRepetitions min max greedy r)
  | .classes cs => (index, .classes cs)
  | .perl pc => (index, .classes ⟨false, #[Class.perl pc]⟩)
  | .dot => (index, .classes ⟨false, #[Class.beforeLineBreak, Class.afterLineBreak]⟩)

def Ast.toRegex (ast : Ast) : Expr := (ast.toRegexAux 0).2

end Regex.Syntax.Parser
