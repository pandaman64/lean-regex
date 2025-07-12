import Regex.Regex
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.NFA.Compile
import RegexCorrectness.Syntax.Ast
import RegexCorrectness.Backtracker
import RegexCorrectness.VM
import RegexCorrectness.Regex.OptimizationInfo

set_option autoImplicit false

open Regex.Data (Expr)
open String (Pos Iterator)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates)

namespace Regex

def IsSearchRegex (re : Regex) : Prop :=
  ∃ e : Expr,
    re.nfa = NFA.compile (.group 0 e) ∧
    Expr.Disjoint (.group 0 e) ∧
    re.maxTag = re.nfa.maxTag ∧
    re.optimizationInfo = .fromExpr (.group 0 e)

namespace IsSearchRegex

theorem of_fromExpr {e : Expr} (h : Expr.Disjoint (.group 0 e)) : IsSearchRegex (.fromExpr (.group 0 e)) := by
  simp [fromExpr]
  exact ⟨e, rfl, h, rfl, rfl⟩

theorem of_parse {s : String} {re : Regex} (h : Regex.parse s = .ok re) :
  IsSearchRegex re := by
  simp [Regex.parse, Regex.Syntax.Parser.parse] at h
  set parseResult := Regex.Syntax.Parser.parseAst s
  match h' : parseResult with
  | .ok ast =>
    simp [Except.map] at h
    have ⟨e, eq⟩ := Regex.Syntax.Parser.Ast.toRegex_group_of_group ast
    have disj : Expr.Disjoint (.group 0 e) :=
      eq ▸ Regex.Syntax.Parser.Ast.toRegex_disjoint (.group ast)
    rw [←h, eq]
    exact of_fromExpr disj
  | .error e => simp [Except.map] at h

noncomputable def inner {re : Regex} (s : IsSearchRegex re) : Expr :=
  s.choose

noncomputable def expr {re : Regex} (s : IsSearchRegex re) : Expr :=
  .group 0 s.inner

theorem nfa_eq {re : Regex} (s : IsSearchRegex re) : re.nfa = NFA.compile s.expr :=
  s.choose_spec.1

theorem disj {re : Regex} (s : IsSearchRegex re) : Expr.Disjoint s.expr :=
  s.choose_spec.2.1

theorem maxTag_eq {re : Regex} (s : IsSearchRegex re) : re.maxTag = re.nfa.maxTag :=
  s.choose_spec.2.2.1

theorem optimizationInfo_eq {re : Regex} (s : IsSearchRegex re) : re.optimizationInfo = .fromExpr s.expr :=
  s.choose_spec.2.2.2

theorem le_maxTag {re : Regex} (s : IsSearchRegex re) : 1 ≤ re.maxTag := by
  simp [s.maxTag_eq]
  show 2 * 0 < re.nfa.maxTag
  apply NFA.lt_of_mem_tags_compile s.nfa_eq.symm
  simp [expr, Expr.tags]

theorem captureNextBuf_soundness' {re bufferSize it matched} (h : re.captureNextBuf bufferSize it = .some matched)
  (s : IsSearchRegex re) (v : it.Valid) :
  ∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    s.expr.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matched := by
  if bt : re.useBacktracker then
    simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
    have ⟨it', it'', groups, eqs, le, c, eqv⟩ := Backtracker.captureNext_soundness s.disj h (OptimizationInfo.valid_findStart_of_valid v)
    exact ⟨it', it'', groups, by grind, Nat.le_trans OptimizationInfo.findStart_le_pos le, c, eqv⟩
  else
    simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
    have ⟨it', it'', groups, eqs, le, c, eqv⟩ := VM.captureNext_soundness s.disj h (OptimizationInfo.valid_findStart_of_valid v)
    exact ⟨it', it'', groups, by grind, Nat.le_trans OptimizationInfo.findStart_le_pos le, c, eqv⟩

theorem captureNextBuf_soundness {re bufferSize it matched} (h : re.captureNextBuf bufferSize it = .some matched)
  (s : IsSearchRegex re) (v : it.Valid) (le : 2 ≤ bufferSize) :
  ∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    s.expr.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matched ∧
    matched[0] = .some it'.pos ∧
    matched[1] = .some it''.pos := by
  have ⟨it', it'', groups, eqs, le', c, eqv⟩ := captureNextBuf_soundness' h s v
  refine ⟨it', it'', groups, eqs, le', c, eqv, ?_⟩

  cases c with
  | @group _ _ groups' _ _ c' =>
    simp [materializeRegexGroups, EquivMaterializedUpdate] at eqv
    have eqv := eqv 0
    have h₁ : 0 < bufferSize := Nat.lt_of_lt_of_le (by decide) le
    have h₂ : 1 < bufferSize := Nat.lt_of_lt_of_le (by decide) le
    simp [h₁, h₂] at eqv
    exact ⟨eqv.1.symm, eqv.2.symm⟩

theorem captureNextBuf_completeness' {re bufferSize it} (h : re.captureNextBuf bufferSize it = .none)
  (s : IsSearchRegex re) (v : it.Valid) (it' it'' : Iterator) (groups : Data.CaptureGroups)
  (eqs : it'.toString = it.toString) (le : it.pos ≤ it'.pos) (c : s.expr.Captures it' it'' groups) :
  False := by
  have : it'.pos < (re.optimizationInfo.findStart it).pos ∨ (re.optimizationInfo.findStart it).pos ≤ it'.pos :=
    Nat.lt_or_ge _ _
  cases this with
  | inl lt => exact OptimizationInfo.findStart_completeness s.optimizationInfo_eq v eqs le lt c
  | inr ge =>
    if bt : re.useBacktracker then
      simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
      exact Backtracker.captureNext_completeness' h (OptimizationInfo.valid_findStart_of_valid v) it' it'' groups (by grind) ge c
    else
      simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
      exact VM.captureNext_completeness' h (OptimizationInfo.valid_findStart_of_valid v) it' it'' groups (by grind) ge c

theorem captureNextBuf_completeness {re bufferSize it} (h : re.captureNextBuf bufferSize it = .none)
  (s : IsSearchRegex re) (v : it.Valid) :
  ¬∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    s.expr.Captures it' it'' groups := by
  grind [captureNextBuf_completeness']

theorem searchNext_some {re it str} (h : re.searchNext it = .some str)
  (s : IsSearchRegex re) (v : it.Valid) :
  ∃ it' it'' groups,
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    s.expr.Captures it' it'' groups ∧
    str.startPos = it'.pos ∧
    str.stopPos = it''.pos := by
  simp [Regex.searchNext] at h
  match h' : re.captureNextBuf 2 it with
  | .none => simp [h'] at h
  | .some matched =>
    have ⟨it', it'', groups, eqs, le, c, eqv, eq₁, eq₂⟩ := captureNextBuf_soundness h' s v (Nat.le_refl _)
    simp [h', eq₁, eq₂] at h
    exact ⟨it', it'', groups, eqs, le, c, by simp [←h]⟩

end IsSearchRegex

end Regex
