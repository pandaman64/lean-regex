import Regex.NFA.Compile.Basic

open Regex.Data (Classes Expr)

set_option autoImplicit false

namespace Regex.NFA.Compile

class ProofData where
  nfa : NFA
  next : Nat
  e : Expr

namespace ProofData

variable [ProofData]

def nfa' : NFA := nfa.pushRegex next e

theorem size_lt : nfa.nodes.size < nfa'.nodes.size := (nfa.pushRegex next e).property

theorem eq_result {result} (eq : NFA.pushRegex nfa next e = result) : result = ⟨nfa', size_lt⟩ := by
  simp [←eq]
  rfl

theorem eq : (nfa.pushRegex next e).val = nfa' := rfl

end ProofData

namespace ProofData

class Empty extends ProofData where
  expr_eq : e = .empty

namespace Empty

def intro {nfa next result} (_ : NFA.pushRegex nfa next .empty = result) : Empty :=
  { nfa, next, e := .empty, expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) : Empty :=
  { nfa, next, e := .empty, expr_eq := rfl }

variable [Empty]

theorem eq' : nfa' = (nfa.pushRegex next .empty).val := by
  simp [nfa', expr_eq]

theorem start_eq : nfa'.start = nfa.nodes.size := by
  simp [eq', pushRegex]

theorem size_eq : nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : nfa'[nfa.nodes.size]'size_lt = .fail := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else nfa'[i] = .fail := by
  split
  case isTrue => exact get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [size_eq] at h
      omega
    simp [this, get_eq]

end Empty

class Epsilon extends ProofData where
  expr_eq : e = .epsilon

namespace Epsilon

def intro {nfa next result} (_ : NFA.pushRegex nfa next .epsilon = result) : Epsilon :=
  { nfa, next, e := .epsilon, expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) : Epsilon :=
  { nfa, next, e := .epsilon, expr_eq := rfl }

variable [Epsilon]

theorem eq' : nfa' = (nfa.pushRegex next .epsilon).val := by
  simp [nfa', expr_eq]

theorem start_eq : nfa'.start = nfa.nodes.size := by
  simp [eq', pushRegex]

theorem size_eq : nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : nfa'[nfa.nodes.size]'size_lt = .epsilon next := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else nfa'[i] = .epsilon next := by
  split
  case isTrue => exact get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [size_eq] at h
      omega
    simp [this, get_eq]

end Epsilon

class Char extends ProofData where
  c : _root_.Char
  expr_eq : e = .char c

namespace Char

def intro {nfa next c result} (_ : NFA.pushRegex nfa next (.char c) = result) : Char :=
  { nfa, next, e := .char c, c, expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) (c : _root_.Char) : Char :=
  { nfa, next, e := .char c, c, expr_eq := rfl }

variable [Char]

theorem eq' : nfa' = (nfa.pushRegex next (.char c)).val := by
  simp [nfa', expr_eq]

theorem start_eq : nfa'.start = nfa.nodes.size := by
  simp [eq', pushRegex]

theorem size_eq : nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : nfa'[nfa.nodes.size]'size_lt = .char c next := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else nfa'[i] = .char c next := by
  split
  case isTrue => exact get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [size_eq] at h
      omega
    simp [this, get_eq]

end Char

class Classes extends ProofData where
  cs : Data.Classes
  expr_eq : e = .classes cs

namespace Classes

def intro {nfa next cs result} (_ : NFA.pushRegex nfa next (.classes cs) = result) : Classes :=
  { nfa, next, e := .classes cs, cs, expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) (cs : Data.Classes) : Classes :=
  { nfa, next, e := .classes cs, cs, expr_eq := rfl }

variable [Classes]

theorem eq' : nfa' = (nfa.pushRegex next (.classes cs)).val := by
  simp [nfa', expr_eq]

theorem start_eq : nfa'.start = nfa.nodes.size := by
  simp [eq', pushRegex]

theorem size_eq : nfa'.nodes.size = nfa.nodes.size + 1 := by
  simp [eq', pushRegex]

theorem get_lt {i : Nat} (h : i < nfa.nodes.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

theorem get_eq : nfa'[nfa.nodes.size]'size_lt = .sparse cs next := by
  simp [eq', pushRegex]

theorem get (i : Nat) (h : i < nfa'.nodes.size) :
  if _ : i < nfa.nodes.size then nfa'[i] = nfa[i]
  else nfa'[i] = .sparse cs next := by
  split
  case isTrue => exact get_lt _
  case isFalse h' =>
    have : i = nfa.nodes.size := by
      simp [size_eq] at h
      omega
    simp [this, get_eq]

end Classes

class Group extends ProofData where
  tag : Nat
  e' : Expr
  expr_eq : e = .group tag e'

namespace Group

def intro {nfa next tag e' result} (_ : NFA.pushRegex nfa next (.group tag e') = result) : Group :=
  { nfa, next, e := .group tag e', tag, e', expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) (tag : Nat) (e' : Expr) : Group :=
  { nfa, next, e := .group tag e', tag, e', expr_eq := rfl }

variable [Group]

def nfaClose : NFA := nfa.pushNode (.save (2 * tag + 1) next)
def nfaExpr : NFA := nfaClose.pushRegex nfaClose.start e'

theorem nfaClose_property : nfa.nodes.size < nfaClose.nodes.size :=
  (nfa.pushNode (.save (2 * tag + 1) next)).property

theorem nfaExpr_property : nfaClose.nodes.size < nfaExpr.nodes.size :=
  (nfaClose.pushRegex nfaClose.start e').property

theorem eq' : nfa' = (nfa.pushRegex next (.group tag e')).val := by
  simp [nfa', expr_eq]

theorem eq_push : nfa' = nfaExpr.pushNode (.save (2 * tag) nfaExpr.start) := eq'

theorem start_eq : nfa'.start = nfaExpr.nodes.size := by
  simp [eq_push]

theorem size_lt_expr' : nfaExpr.nodes.size < nfa'.nodes.size := by
  simp [eq_push]

theorem size_lt_close' : nfaClose.nodes.size < nfa'.nodes.size :=
  Nat.lt_trans nfaExpr_property size_lt_expr'

theorem size_lt_nfa_expr : nfa.nodes.size < nfaExpr.nodes.size :=
  Nat.lt_trans nfaClose_property nfaExpr_property

theorem get_open : nfa'[nfaExpr.nodes.size]'size_lt_expr' = (.save (2 * tag) nfaExpr.start) := by
  simp [eq_push]

theorem get_lt_expr {i : Nat} (h : i < nfaExpr.nodes.size) :
  nfa'[i]'(Nat.lt_trans h size_lt_expr') = nfaExpr[i] := by
  simp [eq_push, pushNode_get_lt i h]

-- We state this for `nfaClose` for now because an inducion hypothesis is needed to see through `nfaExpr`.
theorem get_close_pre : nfaClose[nfa.nodes.size]'nfaClose_property = .save (2 * tag + 1) next := by
  simp [nfaClose]

end Group

class Alternate extends ProofData where
  e₁ : Expr
  e₂ : Expr
  expr_eq : e = .alternate e₁ e₂

namespace Alternate

def intro {nfa next e₁ e₂ result} (_ : NFA.pushRegex nfa next (.alternate e₁ e₂) = result) : Alternate :=
  { nfa, next, e := .alternate e₁ e₂, e₁, e₂, expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) (e₁ e₂ : Expr) : Alternate :=
  { nfa, next, e := .alternate e₁ e₂, e₁, e₂, expr_eq := rfl }

variable [Alternate]

def nfa₁ : NFA := nfa.pushRegex next e₁
def nfa₂ : NFA := nfa₁.pushRegex next e₂

theorem nfa₁_property : nfa.nodes.size < nfa₁.nodes.size :=
  (nfa.pushRegex next e₁).property

theorem nfa₂_property : nfa₁.nodes.size < nfa₂.nodes.size :=
  (nfa₁.pushRegex next e₂).property

theorem eq' : nfa' = (nfa.pushRegex next (.alternate e₁ e₂)).val := by
  simp [nfa', expr_eq]

theorem eq_push : nfa' = nfa₂.pushNode (.split nfa₁.start nfa₂.start) := eq'

theorem size_lt₂ : nfa₂.nodes.size < nfa'.nodes.size := by
  simp [eq_push]

theorem size_lt₁ : nfa₁.nodes.size < nfa'.nodes.size :=
  Nat.lt_trans nfa₂_property size_lt₂

theorem get_split : nfa'[nfa₂.nodes.size]'size_lt₂ = .split nfa₁.start nfa₂.start := by
  simp [eq_push]

theorem start_eq : nfa'.start = nfa₂.nodes.size := by
  simp [eq_push]

theorem get_start : nfa'[nfa'.start]'(start_eq ▸ size_lt₂) = .split nfa₁.start nfa₂.start := by
  simp [start_eq, get_split]

end Alternate

class Concat extends ProofData where
  e₁ : Expr
  e₂ : Expr
  expr_eq : e = .concat e₁ e₂

namespace Concat

def intro {nfa next e₁ e₂ result} (_ : NFA.pushRegex nfa next (.concat e₁ e₂) = result) : Concat :=
  { nfa, next, e := .concat e₁ e₂, e₁, e₂, expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) (e₁ e₂ : Expr) : Concat :=
  { nfa, next, e := .concat e₁ e₂, e₁, e₂, expr_eq := rfl }

variable [Concat]

def nfa₂ : NFA := nfa.pushRegex next e₂

theorem nfa₂_property : nfa.nodes.size < nfa₂.nodes.size :=
  (nfa.pushRegex next e₂).property

theorem eq' : nfa' = (NFA.pushRegex nfa next (.concat e₁ e₂)).val := by
  simp [nfa', expr_eq]

theorem eq_push : nfa' = nfa₂.pushRegex nfa₂.start e₁ := by
  simp [eq', pushRegex]
  rfl

theorem size₂_lt : nfa₂.nodes.size < nfa'.nodes.size := by
  simp [eq_push]
  exact (nfa₂.pushRegex nfa₂.start e₁).property

end Concat

class Star extends ProofData where
  e' : Expr
  expr_eq : e = .star e'

namespace Star

def intro {nfa next e' result} (_ : NFA.pushRegex nfa next (.star e') = result) : Star :=
  { nfa, next, e := .star e', e', expr_eq := rfl }

def intro' (nfa : NFA) (next : Nat) (e': Expr) : Star :=
  { nfa, next, e := .star e', e', expr_eq := rfl }

variable [Star]

theorem eq' : nfa' = (NFA.pushRegex nfa next (.star e')).val := by
  simp [nfa', expr_eq]

def nfaPlaceholder : NFA := nfa.pushNode .fail
def nfaExpr : NFA := nfaPlaceholder.pushRegex nfaPlaceholder.start e'

theorem nfaPlaceholder_property : nfa.nodes.size < nfaPlaceholder.nodes.size := by
  simp [nfaPlaceholder]

theorem nfaExpr_property : nfaPlaceholder.nodes.size < nfaExpr.nodes.size :=
  (nfaPlaceholder.pushRegex nfaPlaceholder.start e').property

theorem start_eq : nfa'.start = nfa.nodes.size := by
  rw [eq', pushRegex]

theorem size_eq_expr' : nfa'.nodes.size = nfaExpr.nodes.size := by
  simp [eq', pushRegex]
  rfl

theorem get_start : nfa'[nfa.nodes.size]'size_lt = .split nfaExpr.start next := by
  simp [eq', pushRegex, NFA.get_eq_nodes_get]
  rfl

theorem get_ne_start (i : Nat) (h : i < nfa'.nodes.size) (ne : i ≠ nfa.nodes.size) :
  nfa'[i] = nfaExpr[i]'(size_eq_expr' ▸ h) := by
  simp [eq', pushRegex, NFA.get_eq_nodes_get]
  rw [Array.get_set_ne (h := ne.symm)]
  rfl

end Star

end ProofData

end Regex.NFA.Compile
