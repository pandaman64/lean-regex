import Regex.Regex.OptimizationInfo
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.Data.Expr.Optimization
import RegexCorrectness.Data.String

open Regex.Data (Expr CaptureGroups)
open String (Iterator)
open Std

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
  next cs h =>
    intro lt
    have : ¬(cs.contains it'.curr) := Iterator.find_completeness v it' c.validL eqs ge lt
    simp [eq, fromExpr] at h
    have ⟨_, h₁, h₂⟩ := h
    have : cs.contains it'.curr := by
      rw [← h₂]
      simp only [HashSet.contains_toArray]
      exact Expr.curr_of_captures_of_firstChars_some c h₁
    contradiction
  next => exact Nat.not_lt_of_ge ge

end Regex.OptimizationInfo
