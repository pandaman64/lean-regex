module

public import Regex.NFA.Basic
public import Regex.Strategy
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finite.Prod
import Mathlib.Tactic.DepRewrite
import RegexCorrectness.Data.String

open String (Pos)

public section

namespace Regex.Backtracker.Model

private scoped instance {nfa : NFA} : Finite (Fin nfa.size) := Finite.of_fintype (Fin nfa.size)
private scoped instance {s : String} : Fintype (Pos s) := ⟨⟨Pos.allPositions s, Pos.nodup_allPositions s⟩, Pos.mem_allPositions s⟩
private scoped instance {s : String} : Finite (Pos s) := Finite.of_fintype (Pos s)
private noncomputable scoped instance {s : String} {nfa : NFA} : Fintype (Fin nfa.size × Pos s) := Fintype.ofFinite _

private noncomputable abbrev argUniv (s : String) (nfa : NFA) : Finset (Fin nfa.size × Pos s) := Finset.univ

def captureNextAux {s : String} (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed) (visited : Finset (Fin nfa.size × Pos s))
  (update : σ.Update) (state : Fin nfa.size) (pos : Pos s) :
  (Pos s × Option σ.Update × { visited' : Finset (Fin nfa.size × Pos s) // visited ⊆ visited' }) :=
  if hmem : (state, pos) ∈ visited then
    (pos, .none, ⟨visited, by simp⟩)
  else
    let visited' := insert (state, pos) visited
    have lt₁ : visited.card < (argUniv s nfa).card :=
      Finset.card_lt_card (Finset.ssubset_def.mp ⟨Finset.subset_univ visited, (by grind)⟩)
    have : (argUniv s nfa).card - visited'.card < (argUniv s nfa).card - visited.card := by
      grind only [= Finset.card_insert_of_notMem]
    match hn : nfa[state] with
    | .done => (pos, .some update, ⟨visited', by grind⟩)
    | .fail => (pos, .none, ⟨visited', by grind⟩)
    | .epsilon state' =>
      let (pos, result, visited'') := captureNextAux σ nfa wf visited' update ⟨state', wf.inBounds' state state.isLt hn⟩ pos
      (pos, result, ⟨visited'', by grind⟩)
    | .split state₁ state₂ =>
      have isLt : state₁ < nfa.size ∧ state₂ < nfa.size := wf.inBounds' state state.isLt hn
      match captureNextAux σ nfa wf visited' update ⟨state₁, isLt.1⟩ pos with
      | (pos, .some update', visited') => (pos, .some update', ⟨visited', by grind⟩)
      | (_pos, .none, visited'') =>
        have : (argUniv s nfa).card - visited''.val.card < (argUniv s nfa).card - visited.card := by
          have : visited.card < visited''.val.card :=
            calc visited.card
              _ < visited'.card := by grind only
              _ ≤ visited''.val.card := Finset.card_le_card visited''.property
          grind
        let (pos, result, visited''') := captureNextAux σ nfa wf visited'' update ⟨state₂, isLt.2⟩ pos
        (pos, result, ⟨visited''', by grind⟩)
    | .save offset state' =>
      let (pos, result, visited'') := captureNextAux σ nfa wf visited' (σ.write update offset pos) ⟨state', wf.inBounds' state state.isLt hn⟩ pos
      (pos, result, ⟨visited'', by grind⟩)
    | .anchor a state' =>
      if a.test pos then
        let (pos, result, visited'') := captureNextAux σ nfa wf visited' update ⟨state', wf.inBounds' state state.isLt hn⟩ pos
        (pos, result, ⟨visited'', by grind⟩)
      else
        (pos, .none, ⟨visited', by grind⟩)
    | .char c state' =>
      if h : ∃ ne : pos ≠ s.endPos, pos.get ne = c then
        let (pos, result, visited'') := captureNextAux σ nfa wf visited' update ⟨state', wf.inBounds' state state.isLt hn⟩ (pos.next h.1)
        (pos, result, ⟨visited'', by grind⟩)
      else
        (pos, .none, ⟨visited', by grind⟩)
    | .sparse cs state' =>
      if h : ∃ ne : pos ≠ s.endPos, pos.get ne ∈ cs then
        let (pos, result, visited'') := captureNextAux σ nfa wf visited' update ⟨state', wf.inBounds' state state.isLt hn⟩ (pos.next h.1)
        (pos, result, ⟨visited'', by grind⟩)
      else
        (pos, .none, ⟨visited', by grind⟩)
termination_by (argUniv s nfa).card - visited.card

section

variable {s : String} {σ : Strategy s} {nfa : NFA} {wf : nfa.WellFormed} {visited : Finset (Fin nfa.size × Pos s)}
  {update : σ.Update} {state : Fin nfa.size} {pos : Pos s} {offset state' state₁ state₂ : Nat}
  {a : Regex.Data.Anchor} {c : Char} {cs : Regex.Data.Classes}

@[grind =]
theorem captureNextAux_visited (hmem : (state, pos) ∈ visited) :
  captureNextAux σ nfa wf visited update state pos = (pos, .none, ⟨visited, by simp⟩) := by
  simp [captureNextAux, hmem]

@[grind =]
theorem captureNextAux_done (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .done) :
  captureNextAux σ nfa wf visited update state pos = (pos, .some update, ⟨insert (state, pos) visited, by simp⟩) := by
  grind only [captureNextAux]

@[grind =]
theorem captureNextAux_fail (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .fail) :
  captureNextAux σ nfa wf visited update state pos = (pos, .none, ⟨insert (state, pos) visited, by simp⟩) := by
  grind only [captureNextAux]

@[grind! .]
theorem captureNextAux_epsilon (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .epsilon state') :
  letI result := captureNextAux σ nfa wf (insert (state, pos) visited) update ⟨state', wf.inBounds' state state.isLt hn⟩ pos
  captureNextAux σ nfa wf visited update state pos =
    ⟨result.1, result.2.1, ⟨result.2.2.val, by grind⟩⟩ := by
  grind only [captureNextAux]

@[grind! .]
theorem captureNextAux_split (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .split state₁ state₂) :
  haveI isLt : state₁ < nfa.size ∧ state₂ < nfa.size := wf.inBounds' state state.isLt hn
  letI result₁ := captureNextAux σ nfa wf (insert (state, pos) visited) update ⟨state₁, isLt.1⟩ pos
  letI result₂ := captureNextAux σ nfa wf result₁.2.2 update ⟨state₂, isLt.2⟩ pos
  captureNextAux σ nfa wf visited update state pos =
    if result₁.2.1.isSome then
      ⟨result₁.1, result₁.2.1, ⟨result₁.2.2.val, by grind⟩⟩
    else
      ⟨result₂.1, result₂.2.1, ⟨result₂.2.2.val, by grind⟩⟩ := by
  conv =>
    lhs
    unfold captureNextAux
  simp only [hmem, ↓reduceDIte]
  rw! [hn]
  grind [captureNextAux]

@[grind! .]
theorem captureNextAux_save (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .save offset state') :
  haveI isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
  letI result := captureNextAux σ nfa wf (insert (state, pos) visited) (σ.write update offset pos) ⟨state', isLt⟩ pos
  captureNextAux σ nfa wf visited update state pos =
    ⟨result.1, result.2.1, ⟨result.2.2.val, by grind⟩⟩ := by
  grind only [captureNextAux]

@[grind! .]
theorem captureNextAux_anchor_pos (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .anchor a state') (h : a.test pos) :
  haveI isLt : state' < nfa.size := wf.inBounds' state state.isLt hn
  letI result := captureNextAux σ nfa wf (insert (state, pos) visited) update ⟨state', isLt⟩ pos
  captureNextAux σ nfa wf visited update state pos =
    ⟨result.1, result.2.1, ⟨result.2.2.val, by grind⟩⟩ := by
  grind only [captureNextAux]

@[grind! .]
theorem captureNextAux_anchor_neg (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .anchor a state') (h : ¬a.test pos) :
  captureNextAux σ nfa wf visited update state pos = (pos, .none, ⟨insert (state, pos) visited, by simp⟩) := by
  grind only [captureNextAux]

@[grind! .]
theorem captureNextAux_char_pos (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .char c state') (ne : pos ≠ s.endPos) (hc : pos.get ne = c) :
  letI result := captureNextAux σ nfa wf (insert (state, pos) visited) update ⟨state', wf.inBounds' state state.isLt hn⟩ (pos.next ne)
  captureNextAux σ nfa wf visited update state pos =
    ⟨result.1, result.2.1, ⟨result.2.2.val, by grind⟩⟩ := by
  conv =>
    lhs
    unfold captureNextAux
  simp only [hmem, ↓reduceDIte]
  rw! [hn]
  simp [ne, hc]

@[grind! .]
theorem captureNextAux_char_neg (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .char c state') (h : pos = s.endPos ∨ ∃ ne : pos ≠ s.endPos, pos.get ne ≠ c) :
  captureNextAux σ nfa wf visited update state pos = (pos, .none, ⟨insert (state, pos) visited, by simp⟩) := by
  grind only [captureNextAux]

@[grind! .]
theorem captureNextAux_sparse_pos (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .sparse cs state') (ne : pos ≠ s.endPos) (hc : pos.get ne ∈ cs) :
  letI result := captureNextAux σ nfa wf (insert (state, pos) visited) update ⟨state', wf.inBounds' state state.isLt hn⟩ (pos.next ne)
  captureNextAux σ nfa wf visited update state pos =
    ⟨result.1, result.2.1, ⟨result.2.2.val, by grind⟩⟩ := by
  conv =>
    lhs
    unfold captureNextAux
  simp only [hmem, ↓reduceDIte]
  rw! [hn]
  simp [ne, hc]

@[grind! .]
theorem captureNextAux_sparse_neg (hmem : (state, pos) ∉ visited) (hn : nfa[state] = .sparse cs state') (h : pos = s.endPos ∨ ∃ ne : pos ≠ s.endPos, pos.get ne ∉ cs) :
  captureNextAux σ nfa wf visited update state pos = (pos, .none, ⟨insert (state, pos) visited, by simp⟩) := by
  grind only [captureNextAux]

end

end Regex.Backtracker.Model

end
