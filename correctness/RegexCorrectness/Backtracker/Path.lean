import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open String (Iterator)

namespace Regex.Backtracker

inductive Path (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) : Iterator → Fin nfa.nodes.size → List (Nat × String.Pos) → Prop where
  | init (v : it.Valid) : Path nfa wf it it ⟨nfa.start, wf.start_lt⟩ []
  | more {i j : Fin nfa.nodes.size} {it' it'' update₁ update₂ update₃} (prev : Path nfa wf it it' i update₁) (step : nfa.Step 0 i it' j it'' update₂)
    (equpdate : update₃ = update₁ ++ List.ofOption update₂) :
    Path nfa wf it it'' j update₃

namespace Path

theorem validL {nfa : NFA} {wf : nfa.WellFormed} {it it' i update} (path : Path nfa wf it it' i update) :
  it.Valid := by
  induction path with
  | init v => exact v
  | more prev step equpdate ih => exact ih

theorem validR {nfa : NFA} {wf : nfa.WellFormed} {it it' i update} (path : Path nfa wf it it' i update) :
  it'.Valid := by
  cases path with
  | init v => exact v
  | more _ step => exact step.validR

theorem toString_eq {nfa : NFA} {wf : nfa.WellFormed} {it it' i update} (path : Path nfa wf it it' i update) :
  it'.toString = it.toString := by
  induction path with
  | init => rfl
  | more prev step equpdate ih => rw [step.toString_eq, ih]

theorem eq_or_nfaPath {nfa : NFA} {wf : nfa.WellFormed} {it it' i update} (path : Path nfa wf it it' i update) :
  (it' = it ∧ i.val = nfa.start ∧ update = []) ∨
  nfa.Path 0 nfa.start it i it' update := by
  induction path with
  | init => simp
  | @more i j it' it'' update₁ update₂ update₃ prev step equpdate ih =>
    match ih with
    | .inl ⟨eqit, eqi, equpdate'⟩ =>
      simp [equpdate, equpdate']
      refine .inr (.last (eqit ▸ eqi ▸ step))
    | .inr path =>
      simp [equpdate]
      refine .inr (path.trans (.last step))

theorem nfaPath_of_ne {nfa : NFA} {wf : nfa.WellFormed} {it it' i update} (path : Path nfa wf it it' i update) (ne : i.val ≠ nfa.start) :
  nfa.Path 0 nfa.start it i it' update := by
  simpa [ne] using eq_or_nfaPath path

end Path

end Regex.Backtracker
