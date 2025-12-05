import RegexCorrectness.Data.BVPos
import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open String (ValidPos)
open Regex.Data (BVPos)

namespace Regex.Backtracker

inductive Path {s : String} (nfa : NFA) (wf : nfa.WellFormed) (pos : ValidPos s) : ValidPos s → Fin nfa.nodes.size → List (Nat × ValidPos s) → Prop where
  | init : Path nfa wf pos pos ⟨nfa.start, wf.start_lt⟩ []
  | more {i j : Fin nfa.nodes.size} {pos' pos'' update₁ update₂ update₃} (prev : Path nfa wf pos pos' i update₁) (step : nfa.Step 0 i pos' j pos'' update₂)
    (equpdate : update₃ = update₁ ++ List.ofOption update₂) :
    Path nfa wf pos pos'' j update₃

namespace Path

variable {s : String} {nfa : NFA} {wf : nfa.WellFormed} {pos pos' pos'' : ValidPos s} {i j : Fin nfa.nodes.size}
  {update update₁ update₂ update₃ : List (Nat × ValidPos s)}

theorem le (path : Path nfa wf pos pos' i update) :
  pos ≤ pos' := by
  induction path with
  | init => exact ValidPos.le_refl _
  | more _ step _ ih => exact ValidPos.le_trans ih step.le

theorem eq_or_nfaPath (path : Path nfa wf pos pos' i update) :
  (pos' = pos ∧ i.val = nfa.start ∧ update = []) ∨
  nfa.Path 0 nfa.start pos i pos' update := by
  induction path with
  | init => simp
  | @more i j pos' pos'' update₁ update₂ update₃ prev step equpdate ih =>
    match ih with
    | .inl ⟨eqpos, eqi, equpdate'⟩ =>
      simp [equpdate, equpdate']
      refine .inr (.last (eqpos ▸ eqi ▸ step))
    | .inr path =>
      simp [equpdate]
      refine .inr (path.trans (.last step))

theorem nfaPath_of_ne (path : Path nfa wf pos pos' i update) (ne : i.val ≠ nfa.start) :
  nfa.Path 0 nfa.start pos i pos' update := by
  simpa [ne] using eq_or_nfaPath path

theorem concat_nfaPath {i j : Nat} (isLt : i < nfa.nodes.size)
  (path₁ : Path nfa wf pos pos' ⟨i, isLt⟩ update₁) (path₂ : nfa.Path 0 i pos' j pos'' update₂) (equpdate : update₃ = update₁ ++ update₂) :
  Path nfa wf pos pos'' ⟨j, path₂.lt_right wf⟩ update₃ := by
  induction path₂ generalizing update₁ with
  | @last i it' j it'' update step => exact path₁.more step equpdate
  | @more i it' j it'' k it''' update₂ update₂' step path ih =>
    exact ih (update₁ := update₁ ++ List.ofOption update₂) path.lt (path₁.more step rfl) (by simp [equpdate])

theorem of_nfaPath {i : Nat} (path : nfa.Path 0 nfa.start pos i pos' update) :
  Path nfa wf pos pos' ⟨i, path.lt_right wf⟩ update := by
  have path₁ : Path nfa wf pos pos ⟨nfa.start, wf.start_lt⟩ [] := .init
  exact path₁.concat_nfaPath wf.start_lt path (by simp)

def bvpos' {startPos : ValidPos s} {bvpos : BVPos startPos} {pos' i update}
  (path : Path nfa wf bvpos.current pos' i update) : BVPos startPos :=
  ⟨pos', ValidPos.le_trans bvpos.le path.le⟩

end Path

end Regex.Backtracker
