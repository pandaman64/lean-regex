import Regex.Data.Classes
import Regex.Data.Expr

open Regex.Data (Class Classes PerlClass Expr)

namespace Regex.Syntax.Parser

inductive Ast : Type where
  | empty : Ast
  | epsilon : Ast
  | char : Char → Ast
  | group : Ast → Ast
  | alternate : Ast → Ast → Ast
  | concat : Ast → Ast → Ast
  | star : Ast → Ast
  | classes : Classes → Ast
  | perl : PerlClass → Ast
  | dot : Ast
deriving Inhabited, Repr, DecidableEq

def Ast.toRegexAux (index : Nat) (ast : Ast) : Nat × Expr :=
  match ast with
  | .empty => (index, .empty)
  | .epsilon => (index, .epsilon)
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
  | .star h =>
    let (index', r) := h.toRegexAux index
    (index', .star r)
  | .classes cs => (index, .classes cs)
  | .perl pc => (index, .classes ⟨false, #[Class.perl pc]⟩)
  | .dot => (index, .classes ⟨false, #[Class.beforeLineBreak, Class.afterLineBreak]⟩)

def Ast.toRegex (ast : Ast) : Expr := (ast.toRegexAux 0).2

end Regex.Syntax.Parser
