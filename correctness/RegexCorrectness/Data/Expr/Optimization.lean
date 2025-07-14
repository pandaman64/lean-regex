import Regex.Data.Expr
import RegexCorrectness.Data.Expr.Semantics

namespace Regex.Data.Expr

theorem empty_of_captures_of_nullOnly {it it' groups e} (c : Expr.Captures it it' groups e) (h : e.nullOnly) :
  it' = it := by
  induction c <;> grind [nullOnly]

theorem curr_of_captures_of_firstChar_some {it it' groups e ch} (c : Expr.Captures it it' groups e) (h : e.firstChar = .some ch) :
  it.curr = ch := by
  induction c with
  | sparse | epsilon | anchor | starEpsilon | starConcat  => simp [firstChar] at h
  | char vf => simp_all [vf.curr, firstChar]
  | group _ ih => exact ih h
  | alternateLeft _ ih =>
    simp [firstChar, Option.bind_eq_some_iff] at h
    exact ih h.1
  | alternateRight _ ih =>
    simp [firstChar, Option.bind_eq_some_iff] at h
    exact ih h.2
  | concat c₁ _ ih₁ ih₂ =>
    simp [firstChar] at h
    split at h
    next h' => exact empty_of_captures_of_nullOnly c₁ h' ▸ ih₂ h
    next => exact ih₁ h

end Regex.Data.Expr
