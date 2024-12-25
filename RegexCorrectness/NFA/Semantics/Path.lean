import Regex.NFA
import RegexCorrectness.Data.List
import RegexCorrectness.Data.Span

set_option autoImplicit false

/-
In this file, we treat an NFA as a collection of instructions and give a small-step operational semantics.
-/

namespace Regex.NFA

open Regex.Data (Span)

inductive Step (nfa : NFA) (lb : Nat) : Nat → Span → Nat → Span → Option (Nat × String.Pos) → Prop where
  | epsilon {i j span} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .epsilon j) :
    Step nfa lb i span j span .none
  | splitLeft {i j₁ j₂ span} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) :
    Step nfa lb i span j₁ span .none
  | splitRight {i j₁ j₂ span} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) :
    Step nfa lb i span j₂ span .none
  | save {i j span offset} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .save offset j) :
    Step nfa lb i span j span (.some (offset, span.curr))
  | char {i j l m c r} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .char c j) :
    Step nfa lb i ⟨l, m, c :: r⟩ j ⟨l, c :: m, r⟩ .none
  | sparse {i j l m c r cs} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .sparse cs j) (mem : c ∈ cs):
    Step nfa lb i ⟨l, m, c :: r⟩ j ⟨l, c :: m, r⟩ .none

namespace Step

variable {nfa nfa' : NFA} {lb lb' i span j span' update}

theorem ge (step : nfa.Step lb i span j span' update) : lb ≤ i := by
  cases step <;> assumption

theorem lt (step : nfa.Step lb i span j span' update) : i < nfa.nodes.size := by
  cases step <;> assumption

theorem lt_right (wf : nfa.WellFormed) (step : nfa.Step lb i span j span' update) : j < nfa.nodes.size := by
  have inBounds := wf.inBounds ⟨i, step.lt⟩
  cases step <;> simp_all [Node.inBounds]

theorem eq_left (step : nfa.Step lb i span j span' update) : span'.l = span.l := by
  cases step <;> rfl

theorem cast (step : nfa.Step lb i span j span' update)
  {lt : i < nfa'.nodes.size} (h : nfa[i]'step.lt = nfa'[i]) :
  nfa'.Step lb i span j span' update := by
  cases step with
  | epsilon ge _ eq => exact .epsilon ge lt (h ▸ eq)
  | splitLeft ge _ eq => exact .splitLeft ge lt (h ▸ eq)
  | splitRight ge _ eq => exact .splitRight ge lt (h ▸ eq)
  | save ge _ eq => exact .save ge lt (h ▸ eq)
  | char ge _ eq => exact .char ge lt (h ▸ eq)
  | sparse ge _ eq mem => exact .sparse ge lt (h ▸ eq) mem

theorem liftBound' (ge : lb' ≤ i) (step : nfa.Step lb i span j span' update) :
  nfa.Step lb' i span j span' update := by
  cases step with
  | epsilon _ lt eq => exact .epsilon ge lt eq
  | splitLeft _ lt eq => exact .splitLeft ge lt eq
  | splitRight _ lt eq => exact .splitRight ge lt eq
  | save _ lt eq => exact .save ge lt eq
  | char _ lt eq => exact .char ge lt eq
  | sparse _ lt eq mem => exact .sparse ge lt eq mem

theorem liftBound (le : lb' ≤ lb) (step : nfa.Step lb i span j span' update) :
  nfa.Step lb' i span j span' update :=
  step.liftBound' (Nat.le_trans le step.ge)

theorem iff_done {lt : i < nfa.nodes.size} (eq : nfa[i] = .done) :
  nfa.Step lb i span j span' update ↔ False := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . simp

theorem iff_fail {lt : i < nfa.nodes.size} (eq : nfa[i] = .fail) :
  nfa.Step lb i span j span' update ↔ False := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . simp

theorem iff_epsilon {next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .epsilon next) :
  nfa.Step lb i span j span' update ↔ lb ≤ i ∧ j = next ∧ span' = span ∧ update = .none := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hspan, hupdate⟩
    simp_all
    exact .epsilon ge lt eq

theorem iff_split {next₁ next₂} {lt : i < nfa.nodes.size} (eq : nfa[i] = .split next₁ next₂) :
  nfa.Step lb i span j span' update ↔ lb ≤ i ∧ (j = next₁ ∨ j = next₂) ∧ span' = span ∧ update = .none := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hspan, hupdate⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt eq
    | inr hj =>
      simp_all
      exact .splitRight ge lt eq

theorem iff_save {offset next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .save offset next) :
  nfa.Step lb i span j span' update ↔ lb ≤ i ∧ j = next ∧ span' = span ∧ update = .some (offset, span.curr) := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hspan, hupdate⟩
    simp_all
    exact .save ge lt eq

theorem iff_char {c next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .char c next) :
  nfa.Step lb i span j span' update ↔ ∃ r', span.r = c :: r' ∧ lb ≤ i ∧ j = next ∧ span' = ⟨span.l, c :: span.m, r'⟩ ∧ update = .none := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨r', hspan, ge, hj, hspan', hupdate⟩
    simp_all
    have : span = ⟨span.l, span.m, c :: r'⟩ := by
      simp [←hspan]
    exact this ▸ .char ge lt eq

theorem iff_sparse {cs next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .sparse cs next) :
  nfa.Step lb i span j span' update ↔ ∃ c r', span.r = c :: r' ∧ c ∈ cs ∧ lb ≤ i ∧ j = next ∧ span' = ⟨span.l, c :: span.m, r'⟩ ∧ update = .none := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
    next mem _ => exact ⟨_, _, ⟨rfl, rfl⟩, mem, rfl, rfl⟩
  . intro ⟨c, r', hspan, mem, ge, hj, hspan', hupdate⟩
    simp_all
    have : span = ⟨span.l, span.m, c :: r'⟩ := by
      simp [←hspan]
    exact this ▸ .sparse ge lt eq mem

end Step

/--
A collection of steps in an NFA forms a path.
-/
inductive Path (nfa : NFA) (lb : Nat) : Nat → Span → Nat → Span → List (Nat × String.Pos) → Prop where
  | last {i span j span' update} (step : Step nfa lb i span j span' update) : Path nfa lb i span j span' (List.ofOption update)
  | more {i span j span' k span'' update updates} (step : Step nfa lb i span j span' update) (rest : Path nfa lb j span' k span'' updates) :
    Path nfa lb i span k span'' (update ::ₒ updates)

namespace Path

variable {nfa nfa' : NFA} {lb lb' i span j span' k span'' updates updates₁ updates₂}

theorem ge (path : nfa.Path lb i span j span' updates) : lb ≤ i := by
  cases path with
  | last step => exact step.ge
  | more step => exact step.ge

theorem lt (path : nfa.Path lb i span j span' updates) : i < nfa.nodes.size := by
  cases path with
  | last step => exact step.lt
  | more step => exact step.lt

/--
A simpler casting procedure where the equality can be proven easily, e.g., when casting to a larger NFA.
-/
theorem cast (eq : ∀ i, lb ≤ i → (_ : i < nfa.nodes.size) → ∃ _ : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : nfa.Path lb i span j span' updates) :
  nfa'.Path lb i span j span' updates := by
  induction path with
  | last step =>
    have ⟨_, eq⟩ := eq _ step.ge step.lt
    exact .last (step.cast eq)
  | more step _ ih =>
    have ⟨_, eq⟩ := eq _ step.ge step.lt
    exact .more (step.cast eq) ih

/--
A casting procedure that transports a path from a larger NFA to a smaller NFA.
-/
theorem cast' (lt : i < nfa.nodes.size) (size_le : nfa.nodes.size ≤ nfa'.nodes.size) (wf : nfa.WellFormed)
  (eq : ∀ i, lb ≤ i → (lt : i < nfa.nodes.size) → nfa'[i]'(Nat.lt_of_lt_of_le lt size_le) = nfa[i])
  (path : nfa'.Path lb i span j span' updates) :
  nfa.Path lb i span j span' updates := by
  induction path with
  | last step => exact .last (step.cast (eq _ step.ge lt))
  | more step _ ih =>
    have step := step.cast (eq _ step.ge lt)
    have rest := ih (step.lt_right wf)
    exact .more step rest

theorem liftBound (le : lb' ≤ lb) (path : nfa.Path lb i span j span' updates) :
  nfa.Path lb' i span j span' updates := by
  induction path with
  | last step => exact .last (step.liftBound le)
  | more step _ ih => exact .more (step.liftBound le) ih

theorem liftBound' (ge : lb' ≤ i)
  (inv : ∀ {i span j span' update}, lb' ≤ i → lb ≤ j → nfa.Step lb i span j span' update → lb' ≤ j)
  (path : nfa.Path lb i span j span' updates) :
  nfa.Path lb' i span j span' updates := by
  induction path with
  | last step => exact .last (step.liftBound' ge)
  | more step rest ih => exact .more (step.liftBound' ge) (ih (inv ge rest.ge step))

theorem trans (path₁ : nfa.Path lb i span j span' updates₁) (path₂ : nfa.Path lb j span' k span'' updates₂) :
  nfa.Path lb i span k span'' (updates₁ ++ updates₂) := by
  induction path₁ with
  | last step =>
    simp
    exact .more step path₂
  | more step _ ih =>
    simp
    exact .more step (ih path₂)

end Path

end Regex.NFA
