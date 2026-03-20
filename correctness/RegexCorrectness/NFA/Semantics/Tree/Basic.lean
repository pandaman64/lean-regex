module

public import Regex.NFA.Basic
public import Mathlib.Data.Finset.Basic
public import Mathlib.Data.Finset.Insert

open String (Pos)
open Regex (NFA)

public section

namespace Regex.NFA

/--
Shape of an NFA backtracking trace (no indices: states, positions, captures, visited sets
live in `IsValid`).
-/
inductive Tree where
  | visited
  | fail
  | done
  | epsilon (next : Tree)
  | split (t₁ t₂ : Tree)
  | save (offset : Nat) (next : Tree)
  | anchorPass (next : Tree)
  | anchorFail
  | char (next : Tree)
  | charFail
  | sparse (next : Tree)
  | sparseFail
deriving DecidableEq, Inhabited

namespace Tree

inductive IsValid {s : String} (nfa : NFA) :
    Nat → Pos s → List (Nat × Pos s) → Finset (Nat × Pos s) → Tree → Finset (Nat × Pos s) → Prop where
  | visited {i p us visIn visOut}
      (lt : i < nfa.size) (hm : (i, p) ∈ visIn) (hvis : visOut = visIn) :
      IsValid nfa i p us visIn .visited visOut
  | fail {i p us visIn visOut}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .fail) (hvis : visOut = insert (i, p) visIn) :
      IsValid nfa i p us visIn .fail visOut
  | done {i p us visIn visOut}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .done) (hvis : visOut = insert (i, p) visIn) :
      IsValid nfa i p us visIn .done visOut
  | epsilon {i j p us visIn visOut}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .epsilon j) {next : Tree}
      (h : IsValid nfa j p us (insert (i, p) visIn) next visOut) :
      IsValid nfa i p us visIn (.epsilon next) visOut
  | split {i j₁ j₂ p us visIn visMid visOut}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .split j₁ j₂) {t₁ t₂ : Tree}
      (h₁ : IsValid nfa j₁ p us (insert (i, p) visIn) t₁ visMid)
      (h₂ : IsValid nfa j₂ p us visMid t₂ visOut) :
      IsValid nfa i p us visIn (.split t₁ t₂) visOut
  | save {i j p us visIn visOut offset}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .save offset j) {next : Tree}
      (h : IsValid nfa j p (us ++ [(offset, p)]) (insert (i, p) visIn) next visOut) :
      IsValid nfa i p us visIn (.save offset next) visOut
  | anchor {i j p us visIn visOut a}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .anchor a j) (ha : a.test p) {next : Tree}
      (h : IsValid nfa j p us (insert (i, p) visIn) next visOut) :
      IsValid nfa i p us visIn (.anchorPass next) visOut
  | anchorFail {i j p us visIn visOut a}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .anchor a j) (ha : ¬a.test p)
      (hvis : visOut = insert (i, p) visIn) :
      IsValid nfa i p us visIn .anchorFail visOut
  | char {i j p us visIn visOut c}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .char c j) (ne : p ≠ s.endPos) (hc : p.get ne = c)
      {next : Tree}
      (h : IsValid nfa j (p.next ne) us (insert (i, p) visIn) next visOut) :
      IsValid nfa i p us visIn (.char next) visOut
  | charFail {i j p us visIn visOut c}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .char c j)
      (hc : p = s.endPos ∨ ∃ ne : p ≠ s.endPos, p.get ne ≠ c) (hvis : visOut = insert (i, p) visIn) :
      IsValid nfa i p us visIn .charFail visOut
  | sparse {i j p us visIn visOut cs}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .sparse cs j) (ne : p ≠ s.endPos)
      (hc : p.get ne ∈ cs) {next : Tree}
      (h : IsValid nfa j (p.next ne) us (insert (i, p) visIn) next visOut) :
      IsValid nfa i p us visIn (.sparse next) visOut
  | sparseFail {i j p us visIn visOut cs}
      (lt : i < nfa.size) (hm : (i, p) ∉ visIn) (hn : nfa[i] = .sparse cs j)
      (hc : p = s.endPos ∨ ∃ ne : p ≠ s.endPos, p.get ne ∉ cs) (hvis : visOut = insert (i, p) visIn) :
      IsValid nfa i p us visIn .sparseFail visOut

theorem deterministic_isValid {s : String} {nfa : NFA} {i : Nat} {p : Pos s} {us : List (Nat × Pos s)}
    {visIn : Finset (Nat × Pos s)} {t₁ t₂ : Tree} {visOut₁ visOut₂ : Finset (Nat × Pos s)}
    (h₁ : IsValid nfa i p us visIn t₁ visOut₁) (h₂ : IsValid nfa i p us visIn t₂ visOut₂) :
    t₁ = t₂ ∧ visOut₁ = visOut₂ := by
  induction h₁ generalizing t₂ visOut₂ <;> cases h₂ <;> grind [IsValid]

theorem tree_eq_of_isValid {s : String} {nfa : NFA} {i : Nat} {p : Pos s} {us : List (Nat × Pos s)}
    {visIn : Finset (Nat × Pos s)} {t₁ t₂ : Tree} {visOut₁ visOut₂ : Finset (Nat × Pos s)}
    (h₁ : IsValid nfa i p us visIn t₁ visOut₁) (h₂ : IsValid nfa i p us visIn t₂ visOut₂) :
    t₁ = t₂ :=
  (deterministic_isValid h₁ h₂).1

theorem visOut_eq_of_isValid {s : String} {nfa : NFA} {i : Nat} {p : Pos s} {us : List (Nat × Pos s)}
    {visIn : Finset (Nat × Pos s)} {t₁ t₂ : Tree} {visOut₁ visOut₂ : Finset (Nat × Pos s)}
    (h₁ : IsValid nfa i p us visIn t₁ visOut₁) (h₂ : IsValid nfa i p us visIn t₂ visOut₂) :
    visOut₁ = visOut₂ :=
  (deterministic_isValid h₁ h₂).2

theorem lt {s : String} {nfa : NFA} {i : Nat} {p : Pos s} {us : List (Nat × Pos s)}
    {visIn visOut : Finset (Nat × Pos s)} {t : Tree} (h : IsValid nfa i p us visIn t visOut) :
    i < nfa.size := by
  cases h <;> assumption

@[expose, grind =]
def firstMatch {s : String} (p : Pos s) (us : List (Nat × Pos s)) (t : Tree) : Option (Pos s × List (Nat × Pos s)) :=
  match t with
  | .visited => .none
  | .fail => .none
  | .done => .some (p, us)
  | .epsilon next => firstMatch p us next
  | .split t₁ t₂ => firstMatch p us t₁ <|> firstMatch p us t₂
  | .save offset next => firstMatch p (us ++ [(offset, p)]) next
  | .anchorPass next => firstMatch p us next
  | .anchorFail => .none
  | .char next =>
    if h : p ≠ s.endPos then firstMatch (p.next h) us next else .none
  | .charFail => .none
  | .sparse next =>
    if h : p ≠ s.endPos then firstMatch (p.next h) us next else .none
  | .sparseFail => .none

end Tree

end Regex.NFA

end
