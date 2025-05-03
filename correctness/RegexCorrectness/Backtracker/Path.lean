import RegexCorrectness.Data.BoundedIterator
import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open String (Iterator)
open Regex.Data (BoundedIterator)

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

theorem le_pos {nfa : NFA} {wf : nfa.WellFormed} {it it' i update} (path : Path nfa wf it it' i update) :
  it.pos ≤ it'.pos := by
  induction path with
  | init _ => exact Nat.le_refl _
  | more _ step _ ih => exact Nat.le_trans ih step.le_pos

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

def bit' {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit : BoundedIterator startIdx maxIdx} {it' i update}
  (path : Path nfa wf bit.it it' i update) : BoundedIterator startIdx maxIdx :=
  have gem : startIdx ≤ it'.pos.byteIdx := Nat.le_trans bit.ge path.le_pos
  have eqm : maxIdx = it'.toString.endPos.byteIdx := path.toString_eq ▸ bit.eq
  have lem : it'.pos.byteIdx ≤ maxIdx := eqm ▸ path.validR.le_endPos
  ⟨it', gem, lem, eqm⟩

theorem isNextNOf {nfa : NFA} {wf : nfa.WellFormed} {startIdx maxIdx : Nat} {bit bit' : BoundedIterator startIdx maxIdx} {it' i update}
  (eqit' : bit'.it = it') (path : Path nfa wf bit.it it' i update) :
  bit'.IsNextNOf bit := by
  induction path generalizing bit' with
  | init v =>
    have eq : bit' = bit := by
      simp [BoundedIterator.ext_iff, eqit']
    exact ⟨0, by simp [eq, BoundedIterator.nextn]⟩
  | @more i j itm it' update₁ update₂ update₃ prev step equpdate ih =>
    have isNextN := @ih prev.bit' rfl
    match step.it_eq_or_next with
    | .inl eq =>
      have eq' : bit' = prev.bit' := by
        simp [BoundedIterator.ext_iff, eqit', eq, Path.bit']
      simpa [eq'] using isNextN
    | .inr ⟨hnext, eq⟩ =>
      have eq' : bit' = prev.bit'.next hnext := by
        simp [BoundedIterator.ext_iff, eqit', eq, Path.bit', BoundedIterator.next, Iterator.next'_eq_next]
      simpa [eq'] using isNextN.next hnext

end Path

end Regex.Backtracker
