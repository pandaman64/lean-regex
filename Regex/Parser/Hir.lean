import Regex.Regex

namespace Regex.Parser

inductive Hir : Type where
  | empty : Hir
  | epsilon : Hir
  | char : Char → Hir
  | group : Hir → Hir
  | alternate : Hir → Hir → Hir
  | concat : Hir → Hir → Hir
  | star : Hir → Hir
deriving Repr, Inhabited

def Hir.toRegexAux (index : Nat) (hir : Hir) : Nat × Regex :=
  match hir with
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

def Hir.toRegex (h : Hir) : Regex := (h.toRegexAux 0).2

end Regex.Parser
