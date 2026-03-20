module

public import RegexCorrectness.Backtracker.Model.Basic
import all RegexCorrectness.Backtracker.Model.Basic
public import RegexCorrectness.NFA.Semantics.Tree.Basic
import all RegexCorrectness.NFA.Semantics.Tree.Basic

open String (Pos)
open Regex (NFA)
open scoped Regex.Backtracker.Model

public section

namespace Regex.Backtracker.Model

#check captureNextAux.induct

noncomputable def mapVis {s : String} {nfa : NFA} (vis : Finset (Nat × Pos s)) : Finset (Fin nfa.size × Pos s) :=
  { p : Fin nfa.size × Pos s | (p.1.val, p.2) ∈ vis }

@[grind =, simp]
theorem mapVis_insert {s : String} {nfa : NFA} (i : Nat) (p : Pos s) (lt : i < nfa.size) (vis : Finset (Nat × Pos s)) :
  mapVis (insert (i, p) vis) = insert ⟨⟨i, lt⟩, p⟩ (mapVis vis) := by
  grind [mapVis]

@[grind =, simp]
theorem mem_mapVis_iff {s : String} {nfa : NFA} (i : Nat) (p : Pos s) (lt : i < nfa.size) (vis : Finset (Nat × Pos s)) :
  (⟨i, lt⟩, p) ∈ mapVis vis ↔ (i, p) ∈ vis := by
  grind [mapVis]

theorem captureNextAux_some_iff_firstMatch_some {s : String} {nfa : NFA} {wf : nfa.WellFormed}
  {i : Nat} {p : Pos s} {us : List (Nat × Pos s)} {vis : Finset (Nat × Pos s)}
  (t : NFA.Tree s nfa i p us vis) (p' us') :
  t.firstMatch = .some (p', us') ↔
  (captureNextAux (HistoryStrategy s) nfa wf (mapVis vis) us ⟨i, t.lt⟩ p).1 = p' ∧
  (captureNextAux (HistoryStrategy s) nfa wf (mapVis vis) us ⟨i, t.lt⟩ p).2.1 = .some us' := by
  fun_induction NFA.Tree.firstMatch generalizing p' us'
  next => grind
  next => grind
  next i p us vis lt hm hn => grind
  next i p us vis j lt hm hn t ih =>
    rw [captureNextAux_epsilon (by grind) hn, ih p' us', mapVis_insert i p lt vis]
  next i p us vis j₁ j₂ lt hm hn t₁ t₂ ih₁ ih₂ =>
    match eq : t₁.firstMatch with
    | .none =>
      dsimp
      rw [ih₂ p' us', mapVis_insert i p lt vis]
      sorry -- This doesn't work
    | .some (p'', us'') =>
      have ih₁ := (ih₁ p'' us'').mp eq
      rw [mapVis_insert i p lt vis] at ih₁
      rw [captureNextAux_split (by grind) hn]
      simp [ih₁]
  next i p us vis j offset lt hm hn t ih =>
    rw [captureNextAux_save (by grind) hn, ih p' us', mapVis_insert i p lt vis]
    simp
  next i p us vis j a lt hm hn ha t ih =>
    rw [captureNextAux_anchor_pos (by grind) hn ha, ih p' us', mapVis_insert i p lt vis]
  next => grind
  next i p us vis j lt hm ne t hn ih =>
    rw [captureNextAux_char_pos (by grind) hn ne rfl, ih p' us', mapVis_insert i p lt vis]
  next => grind
  next i p us vis j cs lt hm hn ne hc t ih =>
    rw [captureNextAux_sparse_pos (by grind) hn ne hc, ih p' us', mapVis_insert i p lt vis]
  next => grind


end Regex.Backtracker.Model

end
