import Regex.NFA
import RegexCorrectness.NFA.Transition
import RegexCorrectness.Semantics.NFA.Heap
import RegexCorrectness.Semantics.NFA.Span

set_option autoImplicit false

/-
In this file, we treat an NFA as a collection of instructions and give a small-step operational semantics.
-/

-- TODO: maybe move this to `RegexCorrectness.NFA.Semantics`.
namespace Regex.NFA

open Semantics (Span Heap)

inductive Step (nfa : NFA) (lb : Nat) : Nat → Span → Heap → Nat → Span → Heap → Prop where
  | epsilon {i j span heap} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .epsilon j) :
    Step nfa lb i span heap j span heap
  | splitLeft {i j₁ j₂ span heap} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) :
    Step nfa lb i span heap j₁ span heap
  | splitRight {i j₁ j₂ span heap} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) :
    Step nfa lb i span heap j₂ span heap
  | save {i j span heap tag} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .save tag j) :
    Step nfa lb i span heap j span heap[tag := span.curr]
  | char {i j l m c r heap} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .char c j) :
    Step nfa lb i ⟨l, m, c :: r⟩ heap j ⟨l, c :: m, r⟩ heap
  | sparse {i j l m c r heap cs} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .sparse cs j) (mem : c ∈ cs):
    Step nfa lb i ⟨l, m, c :: r⟩ heap j ⟨l, c :: m, r⟩ heap

namespace Step

variable {nfa nfa' : NFA} {lb lb' i span heap j span' heap'}

theorem ge (step : nfa.Step lb i span heap j span' heap') : lb ≤ i := by
  cases step <;> assumption

theorem lt (step : nfa.Step lb i span heap j span' heap') : i < nfa.nodes.size := by
  cases step <;> assumption

theorem eq_left (step : nfa.Step lb i span heap j span' heap') : span'.l = span.l := by
  cases step <;> rfl

theorem cast (step : nfa.Step lb i span heap j span' heap')
  (lt : i < nfa'.nodes.size) (h : nfa[i]'step.lt = nfa'[i]) :
  nfa'.Step  lb i span heap j span' heap' := by
  cases step with
  | epsilon ge _ eq => exact .epsilon ge lt (h ▸ eq)
  | splitLeft ge _ eq => exact .splitLeft ge lt (h ▸ eq)
  | splitRight ge _ eq => exact .splitRight ge lt (h ▸ eq)
  | save ge _ eq => exact .save ge lt (h ▸ eq)
  | char ge _ eq => exact .char ge lt (h ▸ eq)
  | sparse ge _ eq mem => exact .sparse ge lt (h ▸ eq) mem

theorem liftBound' (ge : lb' ≤ i) (step : nfa.Step lb i span heap j span' heap') :
  nfa.Step lb' i span heap j span' heap' := by
  cases step with
  | epsilon _ lt eq => exact .epsilon ge lt eq
  | splitLeft _ lt eq => exact .splitLeft ge lt eq
  | splitRight _ lt eq => exact .splitRight ge lt eq
  | save _ lt eq => exact .save ge lt eq
  | char _ lt eq => exact .char ge lt eq
  | sparse _ lt eq mem => exact .sparse ge lt eq mem

theorem liftBound (le : lb' ≤ lb) (step : nfa.Step lb i span heap j span' heap') :
  nfa.Step lb' i span heap j span' heap' :=
  step.liftBound' (Nat.le_trans le step.ge)

end Step

/--
A collection of steps in an NFA forms a path.
-/
inductive Path (nfa : NFA) (lb : Nat) : Nat → Span → Heap → Nat → Span → Heap → Prop where
  | last {i span heap j span' heap'} (step : Step nfa lb i span heap j span' heap') : Path nfa lb i span heap j span' heap'
  | more {i span heap j span' heap' k span'' heap''} (step : Step nfa lb i span heap j span' heap') (rest : Path nfa lb j span' heap' k span'' heap'') :
    Path nfa lb i span heap k span'' heap''

namespace Path

variable {nfa nfa' : NFA} {lb lb' i span heap j span' heap' k span'' heap''}

theorem ge (path : nfa.Path lb i span heap j span' heap') : lb ≤ i := by
  cases path with
  | last step => exact step.ge
  | more step => exact step.ge

theorem lt (path : nfa.Path lb i span heap j span' heap') : i < nfa.nodes.size := by
  cases path with
  | last step => exact step.lt
  | more step => exact step.lt

/--
A casting procedure where the user can "attach" a property to the originating state when proving equality between two NFAs.
-/
-- TODO: does `inv` ever require `rest` as an argument?
theorem castAttach (P : Nat → Prop) (inv₀ : P i)
  (inv : ∀ {i j span span' heap heap'}, P i → nfa.Step lb i span heap j span' heap' → P j)
  (eq : ∀ i, lb ≤ i → (_ : i < nfa.nodes.size) → P i → ∃ _ : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : nfa.Path lb i span heap j span' heap') :
  nfa'.Path lb i span heap j span' heap' := by
  induction path with
  | last step =>
    have ⟨lt, eq⟩ := eq _ step.ge step.lt inv₀
    exact .last (step.cast lt eq)
  | more step _ ih =>
    have ⟨lt, eq⟩ := eq _ step.ge step.lt inv₀
    have rest := ih (inv inv₀ step)
    exact .more (step.cast lt eq) rest

/--
A simpler casting procedure where the equality can be proven easily, e.g., when casting to a larger NFA.
-/
theorem cast (eq : ∀ i, lb ≤ i → (_ : i < nfa.nodes.size) → ∃ _ : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : nfa.Path lb i span heap j span' heap') :
  nfa'.Path lb i span heap j span' heap' :=
  path.castAttach (fun _ => True) trivial (by intros; trivial) (fun i ge lt _ => eq i ge lt)

theorem castBound (le : lb' ≤ lb) (path : nfa.Path lb i span heap j span' heap') :
  nfa.Path lb' i span heap j span' heap' := by
  induction path with
  | last step => exact .last (step.liftBound le)
  | more step _ ih => exact .more (step.liftBound le) ih

theorem trans (path₁ : nfa.Path lb i span heap j span' heap') (path₂ : nfa.Path lb j span' heap' k span'' heap'') :
  nfa.Path lb i span heap k span'' heap'' := by
  induction path₁ with
  | last step => exact .more step path₂
  | more step _ ih => exact .more step (ih path₂)

end Path
