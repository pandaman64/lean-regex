import Regex.NFA.Compile
import Mathlib.Tactic

open Regex.Data (Classes Expr)

set_option autoImplicit false

namespace Regex.NFA.Compile

class ProofData (nfa : NFA) (next : Fin nfa.nodes.size) (e : Expr) where
  nfa' : NFA
  size_lt : nfa.nodes.size < nfa'.nodes.size
  eq : nfa.pushRegex next e = ⟨nfa', size_lt⟩

namespace ProofData

class Empty (nfa : NFA) (next : Fin nfa.nodes.size) extends ProofData nfa next .empty where

namespace Empty

variable {nfa next result} [data : Empty nfa next]

def intro (eq : NFA.pushRegex nfa next .empty = result) : Empty nfa next :=
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
  }

theorem eq' : data.nfa' = (nfa.pushRegex next .empty).val := by
  simp [data.eq]

theorem start_eq : data.nfa'.start.val = nfa.nodes.size := by
  rw [eq']
  simp [pushRegex]

theorem size_eq : data.nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : data.nfa'[i]'(Nat.lt_trans h data.size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : data.nfa'[nfa.nodes.size]'size_lt = .fail := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < data.nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then data.nfa'[i] = nfa[i]
  else data.nfa'[i] = .fail := by
  split
  case isTrue => exact data.get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [data.size_eq] at h
      omega
    simp [this, data.get_eq]

end Empty

class Epsilon (nfa : NFA) (next : Fin nfa.nodes.size) extends ProofData nfa next .epsilon where

namespace Epsilon

variable {nfa next result} [data : Epsilon nfa next]

def intro (eq : NFA.pushRegex nfa next .epsilon = result) : Epsilon nfa next :=
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
  }

theorem eq' : data.nfa' = (nfa.pushRegex next .epsilon).val := by
  simp [data.eq]

theorem start_eq : data.nfa'.start.val = nfa.nodes.size := by
  rw [eq']
  simp [pushRegex]

theorem size_eq : data.nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : data.nfa'[i]'(Nat.lt_trans h data.size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : data.nfa'[nfa.nodes.size]'size_lt = .epsilon next := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < data.nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then data.nfa'[i] = nfa[i]
  else data.nfa'[i] = .epsilon next := by
  split
  case isTrue => exact data.get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [data.size_eq] at h
      omega
    simp [this, data.get_eq]

end Epsilon

class Char (nfa : NFA) (next : Fin nfa.nodes.size) (c : Char) extends ProofData nfa next (.char c) where

namespace Char

variable {nfa next c result} [data : Char nfa next c]

def intro (eq : NFA.pushRegex nfa next (.char c) = result) : Char nfa next c :=
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
  }

theorem eq' : data.nfa' = (nfa.pushRegex next (.char c)).val := by
  simp [data.eq]

theorem start_eq : data.nfa'.start.val = nfa.nodes.size := by
  rw [eq']
  simp [pushRegex]

theorem size_eq : data.nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : data.nfa'[i]'(Nat.lt_trans h data.size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : data.nfa'[nfa.nodes.size]'size_lt = (.char c next) := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < data.nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then data.nfa'[i] = nfa[i]
  else data.nfa'[i] = (.char c next) := by
  split
  case isTrue => exact data.get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [data.size_eq] at h
      omega
    simp [this, data.get_eq]

end Char

class Classes (nfa : NFA) (next : Fin nfa.nodes.size) (cs : Classes) extends ProofData nfa next (.classes cs) where

namespace Classes

variable {nfa next cs result} [data : Classes nfa next cs]

def intro (eq : NFA.pushRegex nfa next (.classes cs) = result) : Classes nfa next cs :=
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
  }

theorem eq' : data.nfa' = (nfa.pushRegex next (.classes cs)).val := by
  simp [data.eq]

theorem start_eq : data.nfa'.start.val = nfa.nodes.size := by
  rw [eq']
  simp [pushRegex]

theorem size_eq : data.nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : data.nfa'[i]'(Nat.lt_trans h data.size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : data.nfa'[nfa.nodes.size]'size_lt = (.sparse cs next) := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < data.nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then data.nfa'[i] = nfa[i]
  else data.nfa'[i] = (.sparse cs next) := by
  split
  case isTrue => exact data.get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [data.size_eq] at h
      omega
    simp [this, data.get_eq]

end Classes

class Group (nfa : NFA) (next : Fin nfa.nodes.size) (tag : Nat) (e : Expr) extends ProofData nfa next (.group tag e) where
  nfaClose : NFA
  nfaClose_eq : nfaClose = nfa.pushNode (.save (2 * tag + 1) next) (by simp [Node.inBounds]; omega)
  nfaExpr : NFA
  nfaExpr_eq : nfaExpr = nfaClose.pushRegex nfaClose.start e

namespace Group

variable {nfa next tag e result} [data : Group nfa next tag e]

def intro (eq : NFA.pushRegex nfa next (.group tag e) = result) : Group nfa next tag e :=
  let nfaClose : NFA := nfa.pushNode (.save (2 * tag + 1) next) (by simp [Node.inBounds]; omega)
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
    nfaClose,
    nfaClose_eq := rfl,
    nfaExpr := nfaClose.pushRegex nfaClose.start e,
    nfaExpr_eq := rfl,
  }

theorem eq' : data.nfa' = (NFA.pushRegex nfa next (.group tag e)).val := by
  simp [data.eq]

theorem eq_push :
  data.nfa' = NFA.pushNode data.nfaExpr (.save (2 * tag) data.nfaExpr.start) (by simp [Node.inBounds]; omega) := by
  rw [data.eq', data.nfaExpr_eq, data.nfaClose_eq]
  rfl

theorem size_lt_expr' : (@nfaExpr nfa next tag e).nodes.size < data.nfa'.nodes.size := by
  simp [eq_push]

theorem size_lt_close_expr : data.nfaClose.nodes.size < data.nfaExpr.nodes.size := by
  have := (data.nfaClose.pushRegex data.nfaClose.start e).property
  simp [data.nfaExpr_eq, this]

theorem size_lt_close' : data.nfaClose.nodes.size < data.nfa'.nodes.size :=
  Nat.lt_trans size_lt_close_expr size_lt_expr'

theorem size_lt_nfa_close : nfa.nodes.size < data.nfaClose.nodes.size := by
  simp [data.nfaClose_eq]

theorem get_open : data.nfa'[data.nfaExpr.nodes.size]'size_lt_expr' = (.save (2 * tag) data.nfaExpr.start) := by
  simp [eq_push]

-- We state this for `nfaClose` for now because an inducion hypothesis is needed to see through `nfaExpr`.
theorem get_close_pre : data.nfaClose[nfa.nodes.size]'size_lt_nfa_close = .save (2 * tag + 1) next := by
  simp [data.nfaClose_eq]

end Group

class Alternate (nfa : NFA) (next : Fin nfa.nodes.size) (e₁ e₂ : Expr) extends ProofData nfa next (.alternate e₁ e₂) where
  nfa₁ : NFA
  nfa₁_eq : nfa₁ = nfa.pushRegex next e₁
  nfa₁_property : nfa.nodes.size < nfa₁.nodes.size
  nfa₂ : NFA
  nfa₂_eq : nfa₂ = nfa₁.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁_property⟩ e₂
  nfa₂_property : nfa₁.nodes.size < nfa₂.nodes.size

namespace Alternate

variable {nfa next e₁ e₂ result} [data : Alternate nfa next e₁ e₂]

def intro (eq : NFA.pushRegex nfa next (.alternate e₁ e₂) = result) : Alternate nfa next e₁ e₂ :=
  let nfa₁ := nfa.pushRegex next e₁
  let nfa₂ := nfa₁.val.pushRegex ⟨next, Nat.lt_trans next.isLt nfa₁.property⟩ e₂
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
    nfa₁,
    nfa₁_eq := rfl,
    nfa₁_property := nfa₁.property,
    nfa₂,
    nfa₂_eq := rfl,
    nfa₂_property := nfa₂.property,
  }

theorem eq' : data.nfa' = (NFA.pushRegex nfa next (.alternate e₁ e₂)).val := by
  simp [data.eq]

theorem eq_push_lt₁ : data.nfa₁.start < data.nfa₂.nodes.size + 1 :=
  calc
    _ < data.nfa₁.nodes.size := data.nfa₁.start.isLt
    _ < data.nfa₂.nodes.size := data.nfa₂_property
    _ < _ := by omega

theorem eq_push :
  data.nfa' = data.nfa₂.pushNode (.split data.nfa₁.start data.nfa₂.start) (by simp [Node.inBounds]; exact ⟨eq_push_lt₁, by omega⟩) := by
  have nfa₂_eq' {isLt} : ((nfa.pushRegex next e₁).val.pushRegex ⟨next, isLt⟩ e₂) = data.nfa₂ := by
    rw [data.nfa₂_eq]
    congr! <;> simp [data.nfa₁_eq]
  simp [data.eq', pushRegex]
  congr! <;> simp [nfa₂_eq', data.nfa₁_eq]

theorem size_lt₂ : data.nfa₂.nodes.size < data.nfa'.nodes.size := by
  simp [eq_push]

theorem size_lt₁ : data.nfa₁.nodes.size < data.nfa'.nodes.size :=
  Nat.lt_trans data.nfa₂_property size_lt₂

theorem get_split : data.nfa'[data.nfa₂.nodes.size]'size_lt₂ = (.split data.nfa₁.start data.nfa₂.start) := by
  simp [eq_push]

end Alternate

class Concat (nfa : NFA) (next : Fin nfa.nodes.size) (e₁ e₂ : Expr) extends ProofData nfa next (.concat e₁ e₂) where
  nfa₂ : NFA
  nfa₂_eq : nfa₂ = nfa.pushRegex next e₂
  nfa₂_property : nfa.nodes.size < nfa₂.nodes.size

namespace Concat

variable {nfa next e₁ e₂ result} [data : Concat nfa next e₁ e₂]

def intro (eq : NFA.pushRegex nfa next (.concat e₁ e₂) = result) : Concat nfa next e₁ e₂ :=
  let nfa₂ := nfa.pushRegex next e₂
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
    nfa₂,
    nfa₂_eq := rfl,
    nfa₂_property := nfa₂.property,
  }

theorem eq' : data.nfa' = (NFA.pushRegex nfa next (.concat e₁ e₂)).val := by
  simp [data.eq]

theorem eq_push : data.nfa' = data.nfa₂.pushRegex data.nfa₂.start e₁ := by
  simp [data.eq', pushRegex]
  conv =>
    rhs
    rw [data.nfa₂_eq]

end Concat

class Star (nfa : NFA) (next : Fin nfa.nodes.size) (e : Expr) extends ProofData nfa next (.star e) where
  nfa_placeholder : NFA
  nfa_placeholder_eq : nfa_placeholder = nfa.pushNode .fail (by simp)
  nfa_expr : NFA
  nfa_expr_eq : nfa_expr = nfa_placeholder.pushRegex nfa_placeholder.start e

namespace Star

variable {nfa next e result} [data : Star nfa next e]

def intro (eq : NFA.pushRegex nfa next (.star e) = result) : Star nfa next e :=
  let nfa_placeholder := nfa.pushNode .fail (by simp)
  let nfa_expr := nfa_placeholder.val.pushRegex nfa_placeholder.val.start e
  {
    nfa' := result.1,
    size_lt := result.2,
    eq := eq,
    nfa_placeholder,
    nfa_placeholder_eq := rfl,
    nfa_expr,
    nfa_expr_eq := rfl,
  }

theorem eq' : data.nfa' = (NFA.pushRegex nfa next (.star e)).val := by
  simp [data.eq]

-- FIXME: Cannot state theorems about `Fin` one due to confusing errors.
-- def start : Fin data.nfa'.nodes.size := ⟨nfa.nodes.size, isLt⟩
-- where
--   isLt : nfa.nodes.size < data.nfa'.nodes.size := by
--     have := (NFA.pushRegex nfa next (.star e)).property
--     simp [data.eq', this]

theorem eq_start : data.nfa'.start.val = nfa.nodes.size := by
  rw [data.eq', pushRegex]
  simp

theorem size_eq_expr' : data.nfa'.nodes.size = data.nfa_expr.nodes.size := by
  rw [data.eq', pushRegex, data.nfa_expr_eq]
  simp
  congr! <;> simp [data.nfa_placeholder_eq]

def expr_start : Fin data.nfa'.nodes.size := data.nfa_expr.start.cast (size_eq_expr'.symm)

theorem get_start : data.nfa'[nfa.nodes.size]'data.size_lt = .split data.expr_start next := by
  simp [data.eq', pushRegex, NFA.get_eq_nodes_get, expr_start]
  rw [data.nfa_expr_eq]
  congr! <;> simp [data.nfa_placeholder_eq]

theorem get_ne_start (i : Nat) (h : i < data.nfa'.nodes.size) (ne : i ≠ nfa.nodes.size) :
  data.nfa'[i] = data.nfa_expr[i]'(data.size_eq_expr' ▸ h) := by
  simp [data.eq', pushRegex, NFA.get_eq_nodes_get]
  rw [Array.get_set_ne]
  . congr!
    simp only [data.nfa_expr_eq]
    rw [data.nfa_placeholder_eq]
  . rw [←data.nfa_placeholder_eq, ←data.nfa_expr_eq]
    exact data.size_eq_expr' ▸ h
  . simp [ne.symm]

end Star

def intro {nfa next e result} (eq : NFA.pushRegex nfa next e = result) :
  match e with
  | .empty => Empty nfa next
  | .epsilon => Epsilon nfa next
  | .char c => Char nfa next c
  | .classes cs => Classes nfa next cs
  | .group tag e => Group nfa next tag e
  | .alternate e₁ e₂ => Alternate nfa next e₁ e₂
  | .concat e₁ e₂ => Concat nfa next e₁ e₂
  | .star e => Star nfa next e :=
  match e with
  | .empty => Empty.intro eq
  | .epsilon => Epsilon.intro eq
  | .char _ => Char.intro eq
  | .classes _ => Classes.intro eq
  | .group _ _ => Group.intro eq
  | .alternate _ _ => Alternate.intro eq
  | .concat _ _ => Concat.intro eq
  | .star _ => Star.intro eq

end Regex.NFA.Compile.ProofData

open Regex.NFA.Compile.ProofData in
example
  {nfa : Regex.NFA}
  {next : Fin nfa.nodes.size}
  {result : { nfa' // nfa.nodes.size < nfa'.nodes.size }}
  (eq : nfa.pushRegex next .empty = result) : True := by
  have data : Empty nfa next := .intro eq
  have := data.eq
  trivial
