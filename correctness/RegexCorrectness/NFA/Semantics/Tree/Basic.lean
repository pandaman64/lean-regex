module

public import Regex.NFA.Basic
public import RegexCorrectness.Data.Expr.Semantics.GroupMap
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert

open String (Pos)
open Regex.Data.Expr (GroupMap)

public section

namespace Regex.NFA
-- This does not work since `split` needs to use the `visited` set after the left branch is processed for the right branch. (really?)
inductive Tree (s : String) (nfa : NFA) : Nat → Pos s → List (Nat × Pos s) → Finset (Nat × Pos s) → Type where
  | visited {i p us visited} (lt : i < nfa.size) (hm : (i, p) ∈ visited) : Tree s nfa i p us visited
  | fail {i p us visited} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .fail) :
    Tree s nfa i p us visited
  | done {i p us visited} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .done) :
    Tree s nfa i p us visited
  | epsilon {i j p us visited} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .epsilon j)
    (h : Tree s nfa j p us (insert (i, p) visited)) :
    Tree s nfa i p us visited
  | split {i j₁ j₂ p us visited} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .split j₁ j₂)
    (h₁ : Tree s nfa j₁ p us (insert (i, p) visited)) (h₂ : Tree s nfa j₂ p us (insert (i, p) visited)) :
    Tree s nfa i p us visited
  | save {i j p us visited offset} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .save offset j)
    (h : Tree s nfa j p (us ++ [(offset, p)]) (insert (i, p) visited)) :
    Tree s nfa i p us visited
  | anchor {i j p us visited a} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .anchor a j)
    (ha : a.test p) (h : Tree s nfa j p us (insert (i, p) visited)) :
    Tree s nfa i p us visited
  | anchorFail {i j p us visited a} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .anchor a j)
    (ha : ¬a.test p) :
    Tree s nfa i p us visited
  | char {i j p us visited c} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .char c j)
    (ne : p ≠ s.endPos) (hc : p.get ne = c) (h : Tree s nfa j (p.next ne) us (insert (i, p) visited)) :
    Tree s nfa i p us visited
  | charFail {i j p us visited c} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .char c j)
    (hc : p = s.endPos ∨ ∃ ne : p ≠ s.endPos, p.get ne ≠ c) :
    Tree s nfa i p us visited
  | sparse {i j p us visited cs} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .sparse cs j)
    (ne : p ≠ s.endPos) (hc : p.get ne ∈ cs) (h : Tree s nfa j (p.next ne) us (insert (i, p) visited)) :
    Tree s nfa i p us visited
  | sparseFail {i j p us visited cs} (lt : i < nfa.size) (hm : (i, p) ∉ visited) (hn : nfa[i] = .sparse cs j)
    (hc : p = s.endPos ∨ ∃ ne : p ≠ s.endPos, p.get ne ∉ cs) :
    Tree s nfa i p us visited

namespace Tree

@[expose, grind =]
def firstMatch {s nfa i p us visited} (t : Tree s nfa i p us visited) : Option (Pos s × List (Nat × Pos s)) :=
  match t with
  | .visited _ _ => .none
  | .fail _ _ _ => .none
  | .done _ _ _ => .some (p, us)
  | .epsilon _ _ _ h => h.firstMatch
  | .split _ _ _ h₁ h₂ => h₁.firstMatch <|> h₂.firstMatch
  | .save _ _ _ h => h.firstMatch
  | .anchor _ _ _ _ h => h.firstMatch
  | .anchorFail _ _ _ _ => .none
  | .char _ _ _ _ _ h => h.firstMatch
  | .charFail _ _ _ _ => .none
  | .sparse _ _ _ _ _ h => h.firstMatch
  | .sparseFail _ _ _ _ => .none

private def cast {s nfa i i' p p' us us' visited visited'}
  (eqi : i = i') (eqp : p = p') (equs : us = us') (eqv : visited = visited')
  (t : Tree s nfa i p us visited) :
  Tree s nfa i' p' us' visited' :=
  match t with
  | .visited lt hm =>
    .visited (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm)
  | .fail lt hm hn =>
    .fail (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm) (by simpa [eqi] using hn)
  | .done lt hm hn =>
    .done (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm) (by simpa [eqi] using hn)
  | .epsilon lt hm hn t =>
    .epsilon (eqi ▸ lt)
              (eqi ▸ eqp ▸ eqv ▸ hm)
              (by simpa [eqi] using hn)
              (t.cast rfl eqp equs (by simp [eqi, eqp, eqv]))
  | .split lt hm hn t₁ t₂ =>
    .split (eqi ▸ lt)
            (eqi ▸ eqp ▸ eqv ▸ hm)
            (by simpa [eqi] using hn)
            (t₁.cast rfl eqp equs (by simp [eqi, eqp, eqv]))
            (t₂.cast rfl eqp equs (by simp [eqi, eqp, eqv]))
  | .save lt hm hn t =>
    .save (eqi ▸ lt)
          (eqi ▸ eqp ▸ eqv ▸ hm)
          (by simpa [eqi] using hn)
          (t.cast rfl eqp (by simp [eqp, equs]) (by simp [eqi, eqp, eqv]))
  | .anchor lt hm hn ha t =>
    .anchor (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm) (by simpa [eqi] using hn)
            (by simpa [eqp] using ha)
            (t.cast rfl eqp equs (by simp [eqi, eqp, eqv]))
  | .anchorFail lt hm hn ha =>
    .anchorFail (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm)
                (by simpa [eqi] using hn)
                (by simpa [eqp] using ha)
  | .char lt hm hn ne hc t =>
    .char (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm)
          (by simpa [eqi] using hn)
          (by simpa [eqp] using ne)
          (by simpa [eqp] using hc)
          (t.cast rfl (by simp [eqp]) equs (by simp [eqi, eqp, eqv]))
  | .charFail lt hm hn hc =>
    .charFail (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm)
              (by simpa [eqi] using hn)
              (by simpa [eqp] using hc)
  | .sparse lt hm hn ne hc t =>
    .sparse (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm)
            (by simpa [eqi] using hn)
            (by simpa [eqp] using ne)
            (by simpa [eqp] using hc)
            (t.cast rfl (by simp [eqp]) equs (by simp [eqi, eqp, eqv]))
  | .sparseFail lt hm hn hc =>
    .sparseFail (eqi ▸ lt) (eqi ▸ eqp ▸ eqv ▸ hm)
                (by simpa [eqi] using hn)
                (by simpa [eqp] using hc)

private theorem deterministicAux {s nfa i i' p p' us us' visited visited'}
  (eqi : i = i') (eqp : p = p') (equs : us = us') (eqv : visited = visited')
  (t : Tree s nfa i p us visited) (t' : Tree s nfa i' p' us' visited') :
  t.cast eqi eqp equs eqv = t' := by
  induction t generalizing i' p' us' visited' t' with
  | @visited i p us visited lt hm => grind only [Tree, Tree.cast]
  | @fail i p us visited lt hm hn => grind only [Tree, Tree.cast]
  | @done i p us visited lt hm hn => grind only [Tree, Tree.cast]
  | @epsilon i j p us visited lt hm hn t ih =>
    cases t' with
    | @epsilon i' j' p' us' visited' lt' hm' hn' t' =>
      grind only [Tree.cast, ih (by grind) eqp equs (by grind) t']
    | _ => grind only
  | @split i j₁ j₂ p us visited lt hm hn t₁ t₂ ih₁ ih₂ =>
    cases t' with
    | @split i' j₁' j₂' p' us' visited' lt' hm' hn' t₁' t₂' =>
      grind only [Tree.cast, ih₁ (by grind) eqp equs (by grind) t₁', ih₂ (by grind) eqp equs (by grind) t₂']
    | _ => grind only
  | @save i j p us visited offset lt hm hn t ih =>
    cases t' with
    | @save i' j' p' us' visited' offset' lt' hm' hn' t' =>
      grind only [Tree.cast, ih (by grind) eqp (by grind) (by grind) t']
    | _ => grind only
  | @anchor i j p us visited a lt hm hn ha t ih =>
    cases t' with
    | @anchor i' j' p' us' visited' a' lt' hm' hn' ha' t' =>
      grind only [Tree.cast, ih (by grind) eqp (by grind) (by grind) t']
    | _ => grind only
  | anchorFail => grind only [Tree, Tree.cast]
  | @char i j p us visited c lt hm hn ne hc t ih =>
    cases t' with
    | @char i' j' p' us' visited' c' lt' hm' hn' ne' hc' t' =>
      grind only [Tree.cast, ih (by grind) (by grind) equs (by grind) t']
    | _ => grind only
  | charFail  => grind only [Tree, Tree.cast]
  | @sparse i j p us visited cs lt hm hn ne hc t ih =>
    cases t' with
    | @sparse i' j' p' us' visited' cs' lt' hm' hn' ne' hc' t' =>
      grind only [Tree.cast, ih (by grind) (by grind) equs (by grind) t']
    | _ => grind only
  | sparseFail => grind only [Tree, Tree.cast]

private theorem cast_rfl {s nfa i p us visited} (t : Tree s nfa i p us visited) :
  t.cast rfl rfl rfl rfl = t := by
  induction t <;> grind [Tree.cast]

theorem deterministic {s nfa i p us visited} (t₁ t₂ : Tree s nfa i p us visited) :
  t₁ = t₂ :=
  cast_rfl t₁ ▸ deterministicAux rfl rfl rfl rfl t₁ t₂

instance {s nfa i p us visited} : Subsingleton (Tree s nfa i p us visited) := ⟨deterministic⟩

theorem lt {s nfa i p us visited} (t : Tree s nfa i p us visited) : i < nfa.size := by
  induction t <;> assumption

end Tree

end Regex.NFA

end
