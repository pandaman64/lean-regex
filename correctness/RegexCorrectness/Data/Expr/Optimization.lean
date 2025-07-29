import Regex.Data.Expr
import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.Data.HashSet

namespace Regex.Data.Expr

theorem empty_of_captures_of_nullOnly {it it' groups e} (c : Expr.Captures it it' groups e) (h : e.nullOnly) :
  it' = it := by
  induction c <;> grind [nullOnly]

open Std in
theorem curr_of_captures_of_firstChars_some {it it' groups e n cs} (c : Expr.Captures it it' groups e) (h : e.firstChars n = .some cs) :
  cs.contains it.curr := by
  revert cs
  induction c with
  | sparse | epsilon | anchor | starEpsilon | starConcat => simp [firstChars]
  | char vf => simp_all [vf.curr, firstChars, Option.bind_eq_some_iff]
  | group _ _ => simp_all [firstChars, Option.bind_eq_some_iff]
  | alternateLeft c₁ ih =>
    intro cs h
    simp [firstChars, Option.bind_eq_some_iff] at h
    have ⟨_, hcs₁, _, _, hcs⟩ := h
    rw [← hcs]
    simp only [HashSet.contains_iff_mem, HashSet.mem_union_iff]
    left
    exact ih hcs₁
  | alternateRight _ ih =>
    intro cs h
    simp [firstChars, Option.bind_eq_some_iff] at h
    have ⟨_, _, _, hcs₂, hcs⟩ := h
    rw [← hcs]
    simp only [HashSet.contains_iff_mem, HashSet.mem_union_iff]
    right
    exact ih hcs₂
  | concat c₁ _ ih₁ ih₂ =>
    intro cs h
    simp [firstChars] at h
    split at h
    all_goals simp [Option.bind_eq_some_iff] at h
    next h' => exact empty_of_captures_of_nullOnly c₁ h' ▸ ih₂ h.1
    next => exact ih₁ h.1

end Regex.Data.Expr
