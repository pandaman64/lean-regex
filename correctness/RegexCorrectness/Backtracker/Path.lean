import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open Regex.Data (Span)

namespace Regex.Backtracker

inductive Path (nfa : NFA) (wf : nfa.WellFormed) (l r : List Char) : Span → Fin nfa.nodes.size → List (Nat × String.Pos) → Prop where
  | init : Path nfa wf l r ⟨l, [], r⟩ ⟨nfa.start, wf.start_lt⟩ []
  | more {i j : Fin nfa.nodes.size} {span₁ span₂ update₁ update₂ update₃} (prev : Path nfa wf l r span₁ i update₁) (step : nfa.Step 0 i span₁ j span₂ update₂)
    (equpdate : update₃ = update₁ ++ List.ofOption update₂) :
    Path nfa wf l r span₂ j update₃

namespace Path

theorem span_eq {nfa : NFA} {wf : nfa.WellFormed} {l r span i update} (path : Path nfa wf l r span i update) :
  l = span.l ∧ r = span.m.reverse ++ span.r := by
  induction path with
  | init => simp
  | @more i j span₁ span₂ update₁ update₂ update₃ prev step equpdate ih =>
    match step.span_eq_or_next with
    | .inl eq => simp [eq, ih]
    | .inr ⟨c, r', eqr, eq⟩ => simp_all

theorem string_eq {nfa : NFA} {wf : nfa.WellFormed} {l r span i update} (path : Path nfa wf l r span i update) :
  span.toString = ⟨l ++ r⟩ := by
  simp [Span.toString, ←path.span_eq]

theorem eq_or_nfaPath {nfa : NFA} {wf : nfa.WellFormed} {l r span i update} (path : Path nfa wf l r span i update) :
  (span = ⟨l, [], r⟩ ∧ i.val = nfa.start ∧ update = []) ∨
  nfa.Path 0 nfa.start ⟨l, [], r⟩ i span update := by
  induction path with
  | init => simp
  | @more i j span₁ span₂ update₁ update₂ update₃ prev step equpdate ih =>
    match ih with
    | .inl ⟨eqspan, eqi, equpdate'⟩ =>
      simp [equpdate, equpdate']
      refine .inr (.last (eqspan ▸ eqi ▸ step))
    | .inr path =>
      simp [equpdate]
      refine .inr (path.trans (.last step))

theorem nfaPath_of_ne {nfa : NFA} {wf : nfa.WellFormed} {l r span i update} (path : Path nfa wf l r span i update) (ne : i.val ≠ nfa.start) :
  nfa.Path 0 nfa.start ⟨l, [], r⟩ i span update := by
  simpa [ne] using eq_or_nfaPath path

end Path

end Regex.Backtracker
