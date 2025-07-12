import Regex.Regex.OptimizationInfo
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.Data.Expr.Optimization
import RegexCorrectness.Data.String

open Regex.Data (Expr CaptureGroups)
open String (Iterator)

namespace Regex.OptimizationInfo

@[simp, grind =]
theorem findStart_toString {it : Iterator} {opt : OptimizationInfo} : (opt.findStart it).toString = it.toString := by
  unfold findStart
  grind

theorem findStart_le_pos {it : Iterator} {opt : OptimizationInfo} : it.pos ≤ (opt.findStart it).pos := by
  fun_cases findStart opt it
  next => exact Iterator.find_le_pos
  next => exact Nat.le_refl _

theorem valid_findStart_of_valid {it : Iterator} {opt : OptimizationInfo} (v : it.Valid) : (opt.findStart it).Valid := by
  fun_cases findStart opt it
  next => exact Iterator.find_valid_of_valid v
  next => exact v

theorem findStart_completeness {it it' it'' : Iterator} {opt : OptimizationInfo} {groups : CaptureGroups} {e : Expr}
  (eq : opt = .fromExpr e) (v : it.Valid) (eqs : it'.toString = it.toString) (ge : it.pos ≤ it'.pos)
  (lt : it'.pos < (opt.findStart it).pos) (c : e.Captures it' it'' groups) :
  False := by
  revert lt
  fun_cases findStart opt it
  next ch h =>
    intro lt
    have ne := Iterator.find_completeness v it' c.validL eqs ge lt
    simp at ne
    simp [eq, fromExpr] at h
    have eq : it'.curr = ch := Expr.curr_of_captures_of_firstChar_some c h
    exact ne eq
  next => exact Nat.not_lt_of_ge ge

end Regex.OptimizationInfo
