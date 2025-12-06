import Regex.Regex
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.NFA.Compile
import RegexCorrectness.Syntax.Ast
import RegexCorrectness.Backtracker
import RegexCorrectness.VM
import RegexCorrectness.Regex.OptimizationInfo

set_option autoImplicit false

open Regex.Data (Expr)
open String (ValidPos)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates)

namespace Regex

def IsSearchRegex (re : Regex) : Prop :=
  ∃ e : Expr,
    re.nfa = NFA.compile (.group 0 e) ∧
    Expr.Disjoint (.group 0 e) ∧
    re.maxTag = re.nfa.maxTag ∧
    re.optimizationInfo = .fromExpr (.group 0 e)

namespace IsSearchRegex

variable {s : String} {re : Regex} {bufferSize : Nat} {pos : ValidPos s} {matched : Buffer s bufferSize}

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

@[grind →]
theorem le_maxTag {re : Regex} (s : IsSearchRegex re) : 1 ≤ re.maxTag := by
  simp [s.maxTag_eq]
  show 2 * 0 < re.nfa.maxTag
  apply NFA.lt_of_mem_tags_compile s.nfa_eq.symm
  simp [expr, Expr.tags]

@[grind →]
theorem lt_of_mem_tags {re : Regex} {tag : Nat} (s : IsSearchRegex re) (h : tag ∈ s.expr.tags) :
  2 * tag < re.maxTag :=
  s.maxTag_eq ▸ NFA.lt_of_mem_tags_compile s.nfa_eq.symm h

theorem captureNextBuf_soundness' (h : re.captureNextBuf bufferSize pos = .some matched)
  (s : IsSearchRegex re) :
  ∃ pos' pos'' groups,
    pos ≤ pos' ∧
    s.expr.Captures pos' pos'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matched := by
  if bt : re.useBacktracker then
    simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
    have ⟨pos', pos'', groups, le, c, eqv⟩ := Backtracker.captureNext_soundness s.disj h
    exact ⟨pos', pos'', groups, ValidPos.le_trans OptimizationInfo.findStart_le_pos le, c, eqv⟩
  else
    simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
    have ⟨pos', pos'', groups, le, c, eqv⟩ := VM.captureNext_soundness s.disj h
    exact ⟨pos', pos'', groups, ValidPos.le_trans OptimizationInfo.findStart_le_pos le, c, eqv⟩

theorem captureNextBuf_soundness (h : re.captureNextBuf bufferSize pos = .some matched)
  (s : IsSearchRegex re) (le : 2 ≤ bufferSize) :
  ∃ pos' pos'' groups,
    pos ≤ pos' ∧
    s.expr.Captures pos' pos'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matched ∧
    matched[0] = .some pos' ∧
    matched[1] = .some pos'' := by
  have ⟨pos', pos'', groups, le, c, eqv⟩ := captureNextBuf_soundness' h s
  refine ⟨pos', pos'', groups, le, c, eqv, ?_⟩

  cases c with
  | @group _ _ groups' _ _ c' =>
    simp [materializeRegexGroups, EquivMaterializedUpdate] at eqv
    have eqv := eqv 0
    grind

theorem captureNextBuf_completeness' (h : re.captureNextBuf bufferSize pos = .none)
  (isr : IsSearchRegex re) (pos' pos'' : ValidPos s) (groups : Data.CaptureGroups s)
  (le : pos ≤ pos') (c : isr.expr.Captures pos' pos'' groups) :
  False := by
  have : pos' < re.optimizationInfo.findStart pos ∨ re.optimizationInfo.findStart pos ≤ pos' :=
    Nat.lt_or_ge _ _
  cases this with
  | inl lt => exact OptimizationInfo.findStart_completeness isr.optimizationInfo_eq le lt c
  | inr ge =>
    if bt : re.useBacktracker then
      simp only [captureNextBuf, bt, ↓reduceIte, isr.nfa_eq] at h
      exact Backtracker.captureNext_completeness' h pos' pos'' groups ge c
    else
      simp only [captureNextBuf, bt, Bool.false_eq_true, ↓reduceIte, isr.nfa_eq] at h
      exact VM.captureNext_completeness' h pos' pos'' groups ge c

theorem captureNextBuf_completeness (h : re.captureNextBuf bufferSize pos = .none) (isr : IsSearchRegex re) :
  ¬∃ pos' pos'' groups,
    pos ≤ pos' ∧
    isr.expr.Captures pos' pos'' groups := by
  grind [captureNextBuf_completeness']

theorem searchNext_some {slice} (h : re.searchNext pos = .some slice) (isr : IsSearchRegex re) :
  ∃ pos' pos'' groups,
    pos ≤ pos' ∧
    isr.expr.Captures pos' pos'' groups ∧
    slice.startInclusive = (searchNext_str_eq_some h ▸ pos') ∧
    slice.endExclusive = (searchNext_str_eq_some h ▸ pos'') := by
  simp [Regex.searchNext] at h
  match h' : re.captureNextBuf 2 pos with
  | .none => simp [h'] at h
  | .some matched =>
    have ⟨pos', pos'', groups, le, c, eqv, eq₁, eq₂⟩ := captureNextBuf_soundness h' isr (Nat.le_refl _)
    exact ⟨pos', pos'', groups, le, c, by grind, by grind⟩

end IsSearchRegex

end Regex
