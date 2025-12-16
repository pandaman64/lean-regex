import Regex.Regex.OptimizationInfo
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.Data.Expr.Optimization
import RegexCorrectness.Data.String

open Regex.Data (Expr CaptureGroups)
open String (Pos)
open Std

namespace Regex.OptimizationInfo

theorem findStart_le_pos {s : String} {pos : Pos s} {opt : OptimizationInfo} : pos ≤ opt.findStart pos := by
  fun_cases findStart opt pos
  next => exact Regex.Data.String.find_le_pos
  next => exact Pos.le_refl _

theorem findStart_completeness {s : String} {pos pos' pos'' : Pos s} {opt : OptimizationInfo} {groups : CaptureGroups s} {e : Expr}
  (eq : opt = .fromExpr e) (ge : pos ≤ pos') (lt : pos' < opt.findStart pos) (c : e.Captures pos' pos'' groups) :
  False := by
  revert lt
  fun_cases findStart opt pos
  next cs h =>
    intro lt
    have ne : pos' ≠ s.endPos := Pos.ne_endPos_of_lt lt
    have : ¬(cs.contains (pos'.get ne)) := Regex.Data.String.find_completeness ge lt
    simp only [eq, fromExpr, Option.map_eq_some_iff] at h
    have ⟨_, h₁, h₂⟩ := h
    grind [HashSet.contains_toArray, Expr.contains_get_of_captures_of_firstChars_some]
  next => exact Nat.not_lt_of_ge ge

end Regex.OptimizationInfo
