import RegexCorrectness.Data.Expr.Semantics

set_option autoImplicit false

open Regex.Data (Expr CaptureGroups)
open String (Iterator)

namespace RegexCorrectness.Spec

/--
The search problem regex engines intend to solve.

Intuitively, the problem is to find a substring that matches the regex (`e`) after the current position (`it`).

We are interested in the following two properties:

* **Soundness**: when an engine returns a positive result, there must be a match in the later part of the string.
  * Additionally, NFA engines must return the correct capture group buffers corresponding `groups`.
* **Completeness**: when an engine returns a negative result, there must be no match in the later part of the string.
  * By contraposition, if there is a match in the later part of the string, the engine must return a positive result.

In other words, we prove that the regex engines are decision procedures of this search problem.
-/
/-
TODOs:
* complete the proofs
* the third property is the uniqueness of the match.
  In other words, the returned match must be the first one (and greedy/longest based on the chosen semantics)
-/
def SearchProblem (e : Expr) (it : Iterator) : Prop :=
  ∃ (it' it'' : Iterator) (groups : CaptureGroups),
    it'.toString = it.toString ∧
    it.pos ≤ it'.pos ∧
    e.Captures it' it'' groups

end RegexCorrectness.Spec
