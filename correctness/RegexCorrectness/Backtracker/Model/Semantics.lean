module

public import RegexCorrectness.Backtracker.Model.Basic
import all RegexCorrectness.Backtracker.Model.Basic
public import RegexCorrectness.NFA.Semantics.Tree.Basic
import all RegexCorrectness.NFA.Semantics.Tree.Basic

open String (Pos)
open Regex (NFA)

public section

namespace Regex.Backtracker.Model

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

theorem captureNextAux_visOut_of_none {s : String} {nfa : NFA} {wf : nfa.WellFormed}
  {i : Nat} {p : Pos s} {us : List (Nat × Pos s)} {visIn visOut : Finset (Nat × Pos s)} {t : NFA.Tree}
  (h : t.IsValid nfa i p us visIn visOut)
  (hc : (captureNextAux (HistoryStrategy s) nfa wf (mapVis visIn) us ⟨i, t.lt h⟩ p).2.1 = .none) :
  (captureNextAux (HistoryStrategy s) nfa wf (mapVis visIn) us ⟨i, t.lt h⟩ p).2.2.val = mapVis visOut := by
  induction h with
  | visited => grind only [= captureNextAux_visited, = mem_mapVis_iff]
  | fail => grind only [= mapVis_insert, = captureNextAux_fail, = Fin.getElem_fin, = mem_mapVis_iff]
  | done => grind only [= mapVis_insert, = captureNextAux_done, = Fin.getElem_fin, = mem_mapVis_iff]
  | @epsilon i j p us visIn visOut lt hm hn t h ih =>
    rw [mapVis_insert i p lt visIn] at ih
    revert hc
    rw [captureNextAux_epsilon (by grind) hn]
    exact ih
  | @split i j₁ j₂ p us visIn visMid visOut lt hm hn t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    rw [mapVis_insert i p lt visIn] at ih₁
    rw [captureNextAux_split (by grind) hn] at ⊢ hc
    split
    next h => grind only [= Option.isSome_none]
    next h =>
      simp only [HistoryStrategy.update_def, h, Bool.false_eq_true, ↓reduceIte] at hc
      simp only [HistoryStrategy.update_def, Bool.not_eq_true, Option.isSome_eq_false_iff,
        Option.isNone_iff_eq_none] at h
      have ih₁ := ih₁ h
      simp only [HistoryStrategy.update_def]
      rw [ih₁] at ⊢ hc
      exact ih₂ hc
  | @save i j p us visIn visOut offset lt hm hn t h ih =>
    rw [mapVis_insert i p lt visIn] at ih
    rw [captureNextAux_save (by grind) hn] at ⊢ hc
    simp [ih hc]
  | @anchor i j p us visIn visOut a lt hm hn ha t h ih =>
    rw [mapVis_insert i p lt visIn] at ih
    rw [captureNextAux_anchor_pos (by grind) hn ha] at ⊢ hc
    simp [ih hc]
  | anchorFail => grind only [= mapVis_insert, !captureNextAux_anchor_neg, = Fin.getElem_fin, = mem_mapVis_iff]
  | @char i j p us visIn visOut c lt hm hn ne hc' t h ih =>
    rw [mapVis_insert i p lt visIn] at ih
    rw [captureNextAux_char_pos (by grind) hn ne hc'] at ⊢ hc
    simp [ih hc]
  | charFail => grind only [= mapVis_insert, !captureNextAux_char_neg, = Fin.getElem_fin, = mem_mapVis_iff]
  | @sparse i j p us visIn visOut cs lt hm hn ne hc' t h ih =>
    rw [mapVis_insert i p lt visIn] at ih
    rw [captureNextAux_sparse_pos (by grind) hn ne hc'] at ⊢ hc
    simp [ih hc]
  | sparseFail => grind only [= mapVis_insert, !captureNextAux_sparse_neg, = Fin.getElem_fin, = mem_mapVis_iff]

theorem firstMatch_some_iff_captureNext_some {s : String} {nfa : NFA} {wf : nfa.WellFormed}
  {i : Nat} {p : Pos s} {us : List (Nat × Pos s)} {visIn visOut : Finset (Nat × Pos s)} {t : NFA.Tree}
  (h : NFA.Tree.IsValid nfa i p us visIn t visOut) (p' us') :
  NFA.Tree.firstMatch p us t = Option.some (p', us') ↔
  (captureNextAux (HistoryStrategy s) nfa wf (mapVis visIn) us ⟨i, NFA.Tree.lt h⟩ p).1 = p' ∧
  (captureNextAux (HistoryStrategy s) nfa wf (mapVis visIn) us ⟨i, NFA.Tree.lt h⟩ p).2.1 = Option.some us' := by
  fun_induction NFA.Tree.firstMatch p us t generalizing i p' us' visIn visOut with
  | case1 =>
    cases h with
    | visited => grind only [= captureNextAux_visited, = mem_mapVis_iff]
  | case2 =>
    cases h with
    | fail => grind only [= captureNextAux_fail, = Fin.getElem_fin, = mem_mapVis_iff]
  | case3 =>
    cases h with
    | done => grind only [= captureNextAux_done, = Fin.getElem_fin, = mem_mapVis_iff]
  | case4 p us t ih =>
    cases h with
    | epsilon =>
      rename_i j lt hn hm h
      rw [captureNextAux_epsilon (by grind) hn, ih h p' us', mapVis_insert i p lt visIn]
  | case5 p us t₁ t₂ ih₁ ih₂ =>
    cases h with
    | split =>
      rename_i j₁ j₂ visMid lt hn hm h₁ h₂
      match eq : t₁.firstMatch p us with
      | .some (p'', us'') =>
        have ih₁ := (ih₁ h₁ p'' us'').mp eq
        rw [mapVis_insert i p lt visIn] at ih₁
        rw [captureNextAux_split (by grind) hn, ih₁.1, ih₁.2]
        simp
      | .none =>
        dsimp
        rw [captureNextAux_split (by grind) hn, ih₂ h₂ p' us']
        have isLt : j₁ < nfa.size ∧ j₂ < nfa.size := wf.inBounds' i lt hn
        have isNone : (captureNextAux (HistoryStrategy s) nfa wf (mapVis (insert (i, p) visIn)) us ⟨j₁, isLt.1⟩ p).2.1 = .none := by
          match eq' : captureNextAux (HistoryStrategy s) nfa wf (mapVis (insert (i, p) visIn)) us ⟨j₁, isLt.1⟩ p with
          | (_, .none, _) => rfl
          | (p'', .some us'', _) => grind only [ih₁ h₁ p'' us'']
        have hmid := captureNextAux_visOut_of_none h₁ isNone
        rw [mapVis_insert i p lt visIn] at isNone hmid
        simp only [HistoryStrategy.update_def, isNone, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
        rw [hmid]
  | case6 p us offset t ih =>
    cases h with
    | save =>
      rename_i j lt hm hn h
      rw [captureNextAux_save (by grind) hn, ih h p' us', mapVis_insert i p lt visIn]
      simp
  | case7 p u t ih =>
    cases h with
    | anchor =>
      rename_i j a lt hn ha hm h
      rw [captureNextAux_anchor_pos (by grind) hn ha, ih h p' us', mapVis_insert i p lt visIn]
  | case8 =>
    cases h with
    | anchorFail => grind only [!captureNextAux_anchor_neg, = Fin.getElem_fin, = mem_mapVis_iff]
  | case9 p u t ne ih =>
    cases h with
    | char =>
      rename_i j c lt hn _ hc hm h
      rw [captureNextAux_char_pos (by grind) hn ne hc, ih h p' us', mapVis_insert i p lt visIn]
  | case10 =>
    cases h with
    | char => grind only
  | case11 =>
    cases h with
    | charFail =>
      rename_i j c lt hn hc hm hv
      rw [captureNextAux_char_neg (by grind) hn hc]
      grind only
  | case12 p u t ne ih =>
    cases h with
    | sparse =>
      rename_i j cs lt hn _ hc hm h
      rw [captureNextAux_sparse_pos (by grind) hn ne hc, ih h p' us', mapVis_insert i p lt visIn]
  | case13 =>
    cases h with
    | sparse => grind only
  | case14 =>
    cases h with
    | sparseFail =>
      rename_i j cs lt hn hc hm hv
      rw [captureNextAux_sparse_neg (by grind) hn hc]
      grind only

end Regex.Backtracker.Model

end
