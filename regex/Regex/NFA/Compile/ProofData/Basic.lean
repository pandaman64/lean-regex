-- TODO: remove this
module

public import Regex.NFA.Compile.Basic
-- import all Regex.NFA.Compile.Basic
public import Regex.NFA.Compile.Lemmas

open Regex.Data (Classes Expr)

@[expose]
public section

namespace Regex.NFA.Compile

class ProofData where
  nfa : NFA
  next : Nat
  e : Expr

namespace ProofData

variable [ProofData]

@[grind =]
def nfa' : NFA := nfa.pushRegex next e

theorem size_lt : nfa.size < nfa'.size := pushRegex_size_lt

theorem eq_result {result} (eq : NFA.pushRegex nfa next e = result) : result = nfa' := by
  simp [←eq]
  rfl

theorem eq : nfa.pushRegex next e = nfa' := (rfl)

end ProofData

namespace ProofData

class Empty extends ProofData where
  expr_eq : e = .empty

namespace Empty

@[grind =]
def intro {nfa next result} (_ : NFA.pushRegex nfa next .empty = result) : Empty :=
  { nfa, next, e := .empty, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) : Empty :=
  { nfa, next, e := .empty, expr_eq := rfl }

variable [Empty]

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next .empty := by
  simp [nfa', expr_eq]

@[grind =]
theorem start_eq : nfa'.start = nfa.size := by
  simp [eq', pushRegex]

@[grind =]
theorem size_eq : nfa'.size = nfa.size + 1 := by
  simp [eq', pushRegex]

@[grind =]
theorem get_lt {i : Nat} (h : i < nfa.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

@[grind =]
theorem get_eq : nfa'[nfa.size]'size_lt = .fail := by
  simp [eq', pushRegex]

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] = if _ : i < nfa.size then nfa[i] else .fail := by
  grind

end Empty

class Epsilon extends ProofData where
  expr_eq : e = .epsilon

namespace Epsilon

@[grind =]
def intro {nfa next result} (_ : NFA.pushRegex nfa next .epsilon = result) : Epsilon :=
  { nfa, next, e := .epsilon, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) : Epsilon :=
  { nfa, next, e := .epsilon, expr_eq := rfl }

variable [Epsilon]

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next .epsilon := by
  simp [nfa', expr_eq]

@[grind =]
theorem start_eq : nfa'.start = nfa.size := by
  simp [eq', pushRegex]

@[grind =]
theorem size_eq : nfa'.size = nfa.size + 1 := by
  simp [eq', pushRegex]

@[grind =]
theorem get_lt {i : Nat} (h : i < nfa.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

@[grind =]
theorem get_eq : nfa'[nfa.size]'size_lt = .epsilon next := by
  simp [eq', pushRegex]

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] = if _ : i < nfa.size then nfa[i] else .epsilon next := by
  grind

end Epsilon

class Anchor extends ProofData where
  anchor : Data.Anchor
  expr_eq : e = .anchor anchor

namespace Anchor

@[grind =]
def intro {nfa next anchor result} (_ : NFA.pushRegex nfa next (.anchor anchor) = result) : Anchor :=
  { nfa, next, e := .anchor anchor, anchor, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (anchor : Data.Anchor) : Anchor :=
  { nfa, next, e := .anchor anchor, anchor, expr_eq := rfl }

variable [Anchor]

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.anchor anchor) := by
  simp [nfa', expr_eq]

@[grind =]
theorem start_eq : nfa'.start = nfa.size := by
  simp [eq', pushRegex]

@[grind =]
theorem size_eq : nfa'.size = nfa.size + 1 := by
  simp [eq', pushRegex]

@[grind =]
theorem get_lt {i : Nat} (h : i < nfa.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

@[grind =]
theorem get_eq : nfa'[nfa.size]'size_lt = .anchor anchor next := by
  simp [eq', pushRegex]

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] = if _ : i < nfa.size then nfa[i] else .anchor anchor next := by
  grind

end Anchor

class Char extends ProofData where
  c : _root_.Char
  expr_eq : e = .char c

namespace Char

@[grind =]
def intro {nfa next c result} (_ : NFA.pushRegex nfa next (.char c) = result) : Char :=
  { nfa, next, e := .char c, c, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (c : _root_.Char) : Char :=
  { nfa, next, e := .char c, c, expr_eq := rfl }

variable [Char]

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.char c) := by
  simp [nfa', expr_eq]

@[grind =]
theorem start_eq : nfa'.start = nfa.size := by
  simp [eq', pushRegex]

@[grind =]
theorem size_eq : nfa'.size = nfa.size + 1 := by
  simp [eq', pushRegex]

@[grind =]
theorem get_lt {i : Nat} (h : i < nfa.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

@[grind =]
theorem get_eq : nfa'[nfa.size]'size_lt = .char c next := by
  simp [eq', pushRegex]

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] = if _ : i < nfa.size then nfa[i] else .char c next := by
  grind

end Char

class Classes extends ProofData where
  cs : Data.Classes
  expr_eq : e = .classes cs

namespace Classes

@[grind =]
def intro {nfa next cs result} (_ : NFA.pushRegex nfa next (.classes cs) = result) : Classes :=
  { nfa, next, e := .classes cs, cs, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (cs : Data.Classes) : Classes :=
  { nfa, next, e := .classes cs, cs, expr_eq := rfl }

variable [Classes]

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.classes cs) := by
  simp [nfa', expr_eq]

@[grind =]
theorem start_eq : nfa'.start = nfa.size := by
  simp [eq', pushRegex]

@[grind =]
theorem size_eq : nfa'.size = nfa.size + 1 := by
  simp [eq', pushRegex]

@[grind =]
theorem get_lt {i : Nat} (h : i < nfa.size) : nfa'[i]'(Nat.lt_trans h size_lt) = nfa[i] := by
  simp [eq', pushRegex, pushNode_get_lt i h]

@[grind =]
theorem get_eq : nfa'[nfa.size]'size_lt = .sparse cs next := by
  simp [eq', pushRegex]

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] = if _ : i < nfa.size then nfa[i] else .sparse cs next := by
  grind

end Classes

class Group extends ProofData where
  tag : Nat
  e' : Expr
  expr_eq : e = .group tag e'

namespace Group

@[grind =]
def intro {nfa next tag e' result} (_ : NFA.pushRegex nfa next (.group tag e') = result) : Group :=
  { nfa, next, e := .group tag e', tag, e', expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (tag : Nat) (e' : Expr) : Group :=
  { nfa, next, e := .group tag e', tag, e', expr_eq := rfl }

variable [Group]

@[grind =]
def nfaClose : NFA := nfa.pushNode (.save (2 * tag + 1) next)

@[grind =]
def nfaExpr : NFA := nfaClose.pushRegex nfaClose.start e'

theorem nfaClose_property : nfa.size < nfaClose.size := by simp [nfaClose]

theorem nfaExpr_property : nfaClose.size < nfaExpr.size :=
  pushRegex_size_lt

theorem wfClose (wf : nfa.WellFormed) (next_lt : next < nfa.size) : nfaClose.WellFormed := by
  grind

theorem wfExpr (wf : nfa.WellFormed) (next_lt : next < nfa.size) : nfaExpr.WellFormed := by
  grind

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.group tag e') := by
  simp [nfa', expr_eq]

@[grind =]
theorem eq_push : nfa' = nfaExpr.pushNode (.save (2 * tag) nfaExpr.start) := eq'

@[grind =]
theorem start_eq : nfa'.start = nfaExpr.size := by
  simp [eq_push]

theorem size_lt_expr' : nfaExpr.size < nfa'.size := by
  simp [eq_push]

theorem size_lt_close' : nfaClose.size < nfa'.size :=
  Nat.lt_trans nfaExpr_property size_lt_expr'

theorem size_lt_nfa_expr : nfa.size < nfaExpr.size :=
  Nat.lt_trans nfaClose_property nfaExpr_property

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] =
    if _ : i < nfa.size then nfa[i]
    else if i = nfa.size then .save (2 * tag + 1) next
    else if _ : i < nfaExpr.size then nfaExpr[i]
    else .save (2 * tag) nfaExpr.start := by
  grind

end Group

class Alternate extends ProofData where
  e₁ : Expr
  e₂ : Expr
  expr_eq : e = .alternate e₁ e₂

namespace Alternate

@[grind =]
def intro {nfa next e₁ e₂ result} (_ : NFA.pushRegex nfa next (.alternate e₁ e₂) = result) : Alternate :=
  { nfa, next, e := .alternate e₁ e₂, e₁, e₂, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (e₁ e₂ : Expr) : Alternate :=
  { nfa, next, e := .alternate e₁ e₂, e₁, e₂, expr_eq := rfl }

variable [Alternate]

@[grind =]
def nfa₁ : NFA := nfa.pushRegex next e₁

@[grind =]
def nfa₂ : NFA := nfa₁.pushRegex next e₂

theorem nfa₁_property : nfa.size < nfa₁.size :=
  pushRegex_size_lt

theorem nfa₂_property : nfa₁.size < nfa₂.size :=
  pushRegex_size_lt

theorem wf₁ (wf : nfa.WellFormed) (next_lt : next < nfa.size) : nfa₁.WellFormed := by
  grind

theorem wf₂ (wf : nfa.WellFormed) (next_lt : next < nfa.size) : nfa₂.WellFormed := by
  grind

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.alternate e₁ e₂) := by
  simp [nfa', expr_eq]

@[grind =]
theorem eq_push : nfa' = nfa₂.pushNode (.split nfa₁.start nfa₂.start) := eq'

theorem size_lt₂ : nfa₂.size < nfa'.size := by
  simp [eq_push]

theorem size_lt₁ : nfa₁.size < nfa'.size :=
  Nat.lt_trans nfa₂_property size_lt₂

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] =
    if _ : i < nfa.size then nfa[i]
    else if _ : i < nfa₁.size then nfa₁[i]
    else if _ : i < nfa₂.size then nfa₂[i]
    else .split nfa₁.start nfa₂.start := by
  grind

end Alternate

class Concat extends ProofData where
  e₁ : Expr
  e₂ : Expr
  expr_eq : e = .concat e₁ e₂

namespace Concat

@[grind =]
def intro {nfa next e₁ e₂ result} (_ : NFA.pushRegex nfa next (.concat e₁ e₂) = result) : Concat :=
  { nfa, next, e := .concat e₁ e₂, e₁, e₂, expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (e₁ e₂ : Expr) : Concat :=
  { nfa, next, e := .concat e₁ e₂, e₁, e₂, expr_eq := rfl }

variable [Concat]

@[grind =]
def nfa₂ : NFA := nfa.pushRegex next e₂

theorem nfa₂_property : nfa.size < nfa₂.size :=
  pushRegex_size_lt

theorem wf₂ (wf : nfa.WellFormed) (next_lt : next < nfa.size) : nfa₂.WellFormed := by
  grind

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.concat e₁ e₂) := by
  simp [nfa', expr_eq]

@[grind =]
theorem eq_push : nfa' = nfa₂.pushRegex nfa₂.start e₁ := by
  simp [eq', pushRegex]
  rfl

theorem size₂_lt : nfa₂.size < nfa'.size := by
  simp [eq_push]
  exact pushRegex_size_lt

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] =
    if _ : i < nfa.size then nfa[i]
    else if _ : i < nfa₂.size then nfa₂[i]
    else (nfa₂.pushRegex nfa₂.start e₁)[i]'(by grind) := by
  grind

end Concat

class Star extends ProofData where
  greedy : Bool
  e' : Expr
  expr_eq : e = .star greedy e'

namespace Star

@[grind =]
def intro {nfa next greedy e' result} (_ : NFA.pushRegex nfa next (.star greedy e') = result) : Star :=
  { nfa, next, e := .star greedy e', greedy, e', expr_eq := rfl }

@[grind =]
def intro' (nfa : NFA) (next : Nat) (greedy : Bool) (e': Expr) : Star :=
  { nfa, next, e := .star greedy e', greedy, e', expr_eq := rfl }

variable [Star]

@[grind =]
theorem eq' : nfa' = nfa.pushRegex next (.star greedy e') := by
  simp [nfa', expr_eq]

@[grind =]
def nfaPlaceholder : NFA := nfa.pushNode .fail

@[grind =]
def nfaExpr : NFA := nfaPlaceholder.pushRegex nfa.size e'

@[grind =]
def split : Node := if greedy then .split nfaExpr.start next else .split next nfaExpr.start

@[grind =]
def quest : NFA := nfaExpr.pushNode split

@[grind =]
def patched : NFA := ⟨quest.nodes.setIfInBounds nfa.size split⟩

@[grind =]
theorem eq_patched : nfa' = patched := by
  grind

theorem nfaPlaceholder_property : nfa.size < nfaPlaceholder.size := by
  simp [nfaPlaceholder]

theorem nfaExpr_property : nfaPlaceholder.size < nfaExpr.size :=
  pushRegex_size_lt

@[grind =]
theorem size_eq_patched : nfa'.size = patched.size := by
  grind

@[grind =]
theorem size_eq_quest : nfa'.size = quest.size := by
  grind

theorem wfPlaceholder (wf : nfa.WellFormed) : nfaPlaceholder.WellFormed := by
  grind

theorem wfExpr (wf : nfa.WellFormed) : nfaExpr.WellFormed := by
  grind

theorem wfQuest (wf : nfa.WellFormed) (next_lt : next < nfa.size) : quest.WellFormed := by
  grind

theorem wfPatched (wf : nfa.WellFormed) (next_lt : next < nfa.size) : patched.WellFormed :=
  eq_patched ▸ pushRegex_wf wf next_lt

@[grind =]
theorem start_eq : nfa'.start = nfaExpr.size := by
  simp [start, size_eq_quest, quest]

@[grind =]
theorem get (i : Nat) (h : i < nfa'.size) :
  nfa'[i] =
    if _ : i < nfa.size then nfa[i]
    else if i = nfa.size then split
    else if _ : i < nfaExpr.size then nfaExpr[i]
    else split := by
  if h' : i < nfa.size then
    grind
  else if h' : i = nfa.size then
    grind
  else
    conv =>
      lhs
      simp only [eq_patched, patched, get_eq_nodes_get,
        Array.getElem_setIfInBounds_ne (show i < quest.size by grind) (show nfa.size ≠ i by grind)]
      rw [← get_eq_nodes_get]
    grind

@[grind =]
theorem get_start : nfa'[nfa'.start]'(by grind) = split := by
  simp only [get]
  grind

@[grind =]
theorem get_placeholder_start : nfa'[nfaPlaceholder.start]'(by grind) = split := by
  simp only [get]
  grind

end Star

end ProofData

end Regex.NFA.Compile

end
