import Regex.Regex
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.NFA.Compile
import RegexCorrectness.Syntax.Ast
import RegexCorrectness.Backtracker
import RegexCorrectness.VM

set_option autoImplicit false

open Regex.Data (Expr Span)
open String (Pos Iterator)
open Regex.Strategy (EquivMaterializedUpdate materializeRegexGroups materializeUpdates)

namespace Regex

def IsSearchRegex (re : Regex) : Prop :=
  ∃ e : Expr,
    re.nfa = NFA.compile (.group 0 e) ∧
    Expr.Disjoint (.group 0 e) ∧
    re.maxTag = re.nfa.maxTag

namespace IsSearchRegex

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
    exact ⟨e, by simp [←h, eq], disj, by simp [←h]⟩
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
  s.choose_spec.2.2

theorem le_maxTag {re : Regex} (s : IsSearchRegex re) : 1 ≤ re.maxTag := by
  simp [s.maxTag_eq]
  show 2 * 0 < re.nfa.maxTag
  apply NFA.lt_of_mem_tags_compile s.nfa_eq.symm
  simp [expr, Expr.tags]

theorem captures_of_captureNext' {re bufferSize it matched} (h : re.captureNextBuf bufferSize it = .some matched)
  (s : IsSearchRegex re) (v : it.Valid) :
  ∃ it' it'' groups,
    it''.toString = it.toString ∧
    s.expr.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matched := by
  if bt : re.useBacktracker then
    simp [Regex.captureNextBuf, bt, s.nfa_eq] at h
    exact Backtracker.captureNext_correct s.disj h v
  else
    simp [Regex.captureNextBuf, bt] at h
    exact VM.captureNext_correct s.nfa_eq.symm s.disj h v rfl

theorem captures_of_captureNext {re bufferSize it matched} (h : re.captureNextBuf bufferSize it = .some matched)
  (s : IsSearchRegex re) (v : it.Valid) (le : 2 ≤ bufferSize) :
  ∃ it' it'' groups,
    it''.toString = it.toString ∧
    s.expr.Captures it' it'' groups ∧
    EquivMaterializedUpdate (materializeRegexGroups groups) matched ∧
    matched[0] = .some it'.pos ∧
    matched[1] = .some it''.pos := by
  have ⟨it', it'', groups, eqstring, c, eqv⟩ := captures_of_captureNext' h s v
  refine ⟨it', it'', groups, eqstring, c, eqv, ?_⟩

  cases c with
  | @group _ _ groups' _ _ c' =>
    simp [materializeRegexGroups, EquivMaterializedUpdate] at eqv
    have eqv := eqv 0
    have h₁ : 0 < bufferSize := Nat.lt_of_lt_of_le (by decide) le
    have h₂ : 1 < bufferSize := Nat.lt_of_lt_of_le (by decide) le
    simp [h₁, h₂] at eqv
    exact ⟨eqv.1.symm, eqv.2.symm⟩

theorem searchNext_some {re it first last} (h : re.searchNext it = .some (first, last))
  (s : IsSearchRegex re) (v : it.Valid) :
  ∃ it' it'' groups,
    it''.toString = it.toString ∧
    s.expr.Captures it' it'' groups ∧
    first = it'.pos ∧
    last = it''.pos := by
  simp [Regex.searchNext, s.nfa_eq] at h
  match h' : re.captureNextBuf 2 it with
  | .none => simp [h'] at h
  | .some matched =>
    have ⟨it', it'', groups, eqstring, c, eqv, eq₁, eq₂⟩ := captures_of_captureNext h' s v (Nat.le_refl _)
    simp [h', eq₁, eq₂] at h
    exact ⟨it', it'', groups, eqstring, c, by simp [←h]⟩

end IsSearchRegex

end Regex
