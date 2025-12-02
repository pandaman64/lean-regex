import Regex.NFA
import RegexCorrectness.Data.List
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

/-
In this file, we treat an NFA as a collection of instructions and give a small-step operational semantics.
-/

open String (ValidPos)

namespace Regex.NFA

@[grind]
inductive Step {s : String} (nfa : NFA) (lb : Nat) : Nat → ValidPos s → Nat → ValidPos s → Option (Nat × ValidPos s) → Prop where
  | epsilon {i j p} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .epsilon j) :
    Step nfa lb i p j p .none
  | anchor {i j p a} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .anchor a j) (h : a.test p) :
    Step nfa lb i p j p .none
  | splitLeft {i j₁ j₂ p} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) :
    Step nfa lb i p j₁ p .none
  | splitRight {i j₁ j₂ p} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) :
    Step nfa lb i p j₂ p .none
  | save {i j p offset} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .save offset j) :
    Step nfa lb i p j p (.some (offset, p))
  | char {i j p c} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .char c j) (ne : p ≠ s.endValidPos) (eq' : p.get ne = c) :
    Step nfa lb i p j (p.next ne) .none
  | sparse {i j p cs} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .sparse cs j) (ne : p ≠ s.endValidPos) (mem : p.get ne ∈ cs):
    Step nfa lb i p j (p.next ne) .none

namespace Step

variable {s : String} {nfa nfa' : NFA} {lb lb'} {p p' : ValidPos s} {i j k update}

theorem ge (step : nfa.Step lb i p j p' update) : lb ≤ i := by
  cases step <;> assumption

theorem lt (step : nfa.Step lb i p j p' update) : i < nfa.nodes.size := by
  cases step <;> assumption

theorem lt_right (wf : nfa.WellFormed) (step : nfa.Step lb i p j p' update) : j < nfa.nodes.size := by
  have inBounds := wf.inBounds ⟨i, step.lt⟩
  cases step <;> simp_all [Node.inBounds]

theorem eq_or_next (step : nfa.Step lb i p j p' update) : p' = p ∨ ∃ ne : p ≠ s.endValidPos, p' = p.next ne := by
  cases step <;> simp_all

theorem le (step : nfa.Step lb i p j p' update) : p ≤ p' := by
  match step.eq_or_next with
  | .inl eq => exact eq ▸ ValidPos.le_refl _
  | .inr ⟨_, eq⟩ => exact ValidPos.le_of_lt (eq ▸ ValidPos.lt_next p)

theorem cast (step : nfa.Step lb i p j p' update)
  {lt : i < nfa'.nodes.size} (h : nfa[i]'step.lt = nfa'[i]) :
  nfa'.Step lb i p j p' update := by
  cases step with
  | epsilon ge _ eq => exact .epsilon ge lt (h ▸ eq)
  | anchor ge _ eq h' => exact .anchor ge lt (h ▸ eq) h'
  | splitLeft ge _ eq => exact .splitLeft ge lt (h ▸ eq)
  | splitRight ge _ eq => exact .splitRight ge lt (h ▸ eq)
  | save ge _ eq => exact .save ge lt (h ▸ eq)
  | char ge _ eq ne eq' => exact .char ge lt (h ▸ eq) ne eq'
  | sparse ge _ eq ne mem => exact .sparse ge lt (h ▸ eq) ne mem

theorem liftBound' (ge : lb' ≤ i) (step : nfa.Step lb i p j p' update) :
  nfa.Step lb' i p j p' update := by
  cases step with
  | epsilon _ lt eq => exact .epsilon ge lt eq
  | anchor _ lt eq h => exact .anchor ge lt eq h
  | splitLeft _ lt eq => exact .splitLeft ge lt eq
  | splitRight _ lt eq => exact .splitRight ge lt eq
  | save _ lt eq => exact .save ge lt eq
  | char _ lt eq ne eq' => exact .char ge lt eq ne eq'
  | sparse _ lt eq ne mem => exact .sparse ge lt eq ne mem

theorem liftBound (le : lb' ≤ lb) (step : nfa.Step lb i p j p' update) :
  nfa.Step lb' i p j p' update :=
  step.liftBound' (Nat.le_trans le step.ge)

theorem iff_done {lt : i < nfa.nodes.size} (eq : nfa[i] = .done) :
  nfa.Step lb i p j p' update ↔ False := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . simp

theorem iff_fail {lt : i < nfa.nodes.size} (eq : nfa[i] = .fail) :
  nfa.Step lb i p j p' update ↔ False := by
  grind

theorem iff_epsilon {next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .epsilon next) :
  nfa.Step lb i p j p' update ↔ lb ≤ i ∧ j = next ∧ p' = p ∧ update = .none := by
  grind

theorem iff_anchor {anchor next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .anchor anchor next) :
  nfa.Step lb i p j p' update ↔ lb ≤ i ∧ j = next ∧ p' = p ∧ update = .none ∧ anchor.test p := by
  grind

theorem iff_split {next₁ next₂} {lt : i < nfa.nodes.size} (eq : nfa[i] = .split next₁ next₂) :
  nfa.Step lb i p j p' update ↔ lb ≤ i ∧ (j = next₁ ∨ j = next₂) ∧ p' = p ∧ update = .none := by
  grind

theorem iff_save {offset next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .save offset next) :
  nfa.Step lb i p j p' update ↔ lb ≤ i ∧ j = next ∧ p' = p ∧ update = .some (offset, p) := by
  grind

theorem iff_char {c next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .char c next) :
  nfa.Step lb i p j p' update ↔ ∃ ne, lb ≤ i ∧ j = next ∧ p' = p.next ne ∧ update = .none ∧ p.get ne = c := by
  grind

theorem iff_sparse {cs next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .sparse cs next) :
  nfa.Step lb i p j p' update ↔ ∃ ne, lb ≤ i ∧ j = next ∧ p' = p.next ne ∧ update = .none ∧ p.get ne ∈ cs := by
  grind

theorem compile_liftBound {e nfa} (eq : compile e = nfa) (step : nfa.Step 0 i p j p' update) :
  nfa.Step 1 i p j p' update := by
  cases Nat.eq_zero_or_pos i with
  | inl eqi =>
    have lt : i < nfa.nodes.size := eqi ▸ lt_zero_size_compile eq
    have := (done_iff_zero_compile eq ⟨i, lt⟩).mpr eqi
    cases step <;> simp_all
  | inr gt => exact step.liftBound' gt

end Step

/--
A collection of steps in an NFA forms a path. The path must contain at least one step
(which implies that the first state is greater than or equal to the lower bound).
-/
inductive Path {s : String} (nfa : NFA) (lb : Nat) : Nat → ValidPos s → Nat → ValidPos s → List (Nat × ValidPos s) → Prop where
  | last {i p j p' update} (step : Step nfa lb i p j p' update) : Path nfa lb i p j p' (List.ofOption update)
  | more {i p j p' k p'' update updates} (step : Step nfa lb i p j p' update) (rest : Path nfa lb j p' k p'' updates) :
    Path nfa lb i p k p'' (update ::ₒ updates)

namespace Path

variable {s : String} {nfa nfa' : NFA} {lb lb'} {p p' p'' : ValidPos s} {i j k updates updates₁ updates₂}

theorem ge (path : nfa.Path lb i p j p' updates) : lb ≤ i := by
  cases path with
  | last step => exact step.ge
  | more step => exact step.ge

theorem lt (path : nfa.Path lb i p j p' updates) : i < nfa.nodes.size := by
  cases path with
  | last step => exact step.lt
  | more step => exact step.lt

theorem lt_right (wf : nfa.WellFormed) (path : nfa.Path lb i p j p' updates) : j < nfa.nodes.size := by
  induction path with
  | last step => exact step.lt_right wf
  | more _ _ ih => exact ih

theorem le (path : nfa.Path lb i p j p' updates) : p ≤ p' := by
  induction path with
  | last step => exact step.le
  | more step _ ih => exact ValidPos.le_trans step.le ih

/--
A simpler casting procedure where the equality can be proven easily, e.g., when casting to a larger NFA.
-/
theorem cast (eq : ∀ i, lb ≤ i → (_ : i < nfa.nodes.size) → ∃ _ : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : nfa.Path lb i p j p' updates) :
  nfa'.Path lb i p j p' updates := by
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
  (path : nfa'.Path lb i p j p' updates) :
  nfa.Path lb i p j p' updates := by
  induction path with
  | last step => exact .last (step.cast (eq _ step.ge lt))
  | more step _ ih =>
    have step := step.cast (eq _ step.ge lt)
    have rest := ih (step.lt_right wf)
    exact .more step rest

theorem liftBound (le : lb' ≤ lb) (path : nfa.Path lb i p j p' updates) :
  nfa.Path lb' i p j p' updates := by
  induction path with
  | last step => exact .last (step.liftBound le)
  | more step _ ih => exact .more (step.liftBound le) ih

theorem liftBound' (ge : lb' ≤ i)
  (inv : ∀ {p p' : ValidPos s} {i j update}, lb' ≤ i → lb ≤ j → nfa.Step lb i p j p' update → lb' ≤ j)
  (path : nfa.Path lb i p j p' updates) :
  nfa.Path lb' i p j p' updates := by
  induction path with
  | last step => exact .last (step.liftBound' ge)
  | more step rest ih => exact .more (step.liftBound' ge) (ih (inv ge rest.ge step))

theorem trans (path₁ : nfa.Path lb i p j p' updates₁) (path₂ : nfa.Path lb j p' k p'' updates₂) :
  nfa.Path lb i p k p'' (updates₁ ++ updates₂) := by
  induction path₁ with
  | last step =>
    simp
    exact .more step path₂
  | more step _ ih =>
    simp
    exact .more step (ih path₂)

theorem compile_liftBound {e nfa} (eq : compile e = nfa) (path : nfa.Path 0 i p j p' updates) :
  nfa.Path 1 i p j p' updates := by
  induction path with
  | last step => exact .last (step.compile_liftBound eq)
  | more step _ ih => exact .more (step.compile_liftBound eq) ih

/--
If a property is closed under a single step, then it is closed under a path.
-/
theorem of_step_closure {lb} (motive : Nat → ValidPos s → Prop) (closure : ∀ i p j p' update, motive i p → nfa.Step lb i p j p' update → motive j p')
  {i it j it' update} (base : motive i it) (path : nfa.Path lb i it j it' update) :
  motive j it' := by
  induction path with
  | @last i it j it' update step => exact closure i it j it' update base step
  | @more i it j it' k it'' update₁ _ step _ ih => exact ih (closure i it j it' update₁ base step)

end Path

end Regex.NFA
