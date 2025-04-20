import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open Regex.Data (Span)

namespace Regex.Backtracker

inductive Path (nfa : NFA) (wf : nfa.WellFormed) : Span → Fin nfa.nodes.size → List (Nat × String.Pos) → Prop where
  | init {l r} : Path nfa wf ⟨l, [], r⟩ ⟨nfa.start, wf.start_lt⟩ []
  | more {i j : Fin nfa.nodes.size} {span₁ span₂ update₁ update₂ update₃} (prev : Path nfa wf span₁ i update₁) (step : nfa.Step 0 i span₁ j span₂ update₂)
    (equpdate : update₃ = update₁ ++ List.ofOption update₂) :
    Path nfa wf span₂ j update₃

namespace Path

theorem eq_or_nfaPath {nfa : NFA} {wf : nfa.WellFormed} {span i update} (path : Path nfa wf span i update) :
  ∃ l r,
    (span = ⟨l, [], r⟩ ∧ i.val = nfa.start ∧ update = []) ∨
    nfa.Path 0 nfa.start ⟨l, [], r⟩ i span update := by
  induction path with
  | @init l r =>
    exists l, r
    simp
  | @more i j span₁ span₂ update₁ update₂ update₃ prev step equpdate ih =>
    have ⟨l, r, h⟩ := ih
    exists l, r
    match h with
    | .inl ⟨eqspan, eqi, equpdate'⟩ =>
      simp [equpdate, equpdate']
      exact .inr (.last (eqspan ▸ eqi ▸ step))
    | .inr path =>
      simp [equpdate]
      exact .inr (path.trans (.last step))

theorem nfaPath_of_ne {nfa : NFA} {wf : nfa.WellFormed} {span i update} (path : Path nfa wf span i update) (ne : i.val ≠ nfa.start) :
  ∃ l r, nfa.Path 0 nfa.start ⟨l, [], r⟩ i span update := by
  have ⟨l, r, h⟩ := eq_or_nfaPath path
  simp [ne] at h
  exact ⟨l, r, h⟩

end Path

end Regex.Backtracker
