import Regex.NFA
import RegexCorrectness.Data.List
import RegexCorrectness.NFA.Compile

set_option autoImplicit false

/-
In this file, we treat an NFA as a collection of instructions and give a small-step operational semantics.
-/

open String (ValidPos)

namespace Regex.NFA

inductive Step {s : String} (nfa : NFA) (lb : Nat) : Nat → ValidPos s → Nat → ValidPos s → Option (Nat × ValidPos s) → Prop where
  | epsilon {i j it} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .epsilon j) (v : it.Valid) :
    Step nfa lb i it j it .none
  | anchor {i j it a} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .anchor a j) (v : it.Valid) (h : a.test it) :
    Step nfa lb i it j it .none
  | splitLeft {i j₁ j₂ it} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) (v : it.Valid) :
    Step nfa lb i it j₁ it .none
  | splitRight {i j₁ j₂ it} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .split j₁ j₂) (v : it.Valid) :
    Step nfa lb i it j₂ it .none
  | save {i j it offset} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .save offset j) (v : it.Valid) :
    Step nfa lb i it j it (.some (offset, it.pos))
  | char {i j it l c r} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .char c j) (vf : it.ValidFor l (c :: r)) :
    Step nfa lb i it j it.next .none
  | sparse {i j it l c r cs} (ge : lb ≤ i) (lt : i < nfa.nodes.size) (eq : nfa[i] = .sparse cs j) (vf : it.ValidFor l (c :: r)) (mem : c ∈ cs):
    Step nfa lb i it j it.next .none

namespace Step

variable {nfa nfa' : NFA} {lb lb' i it j it' update}

theorem ge (step : nfa.Step lb i it j it' update) : lb ≤ i := by
  cases step <;> assumption

theorem lt (step : nfa.Step lb i it j it' update) : i < nfa.nodes.size := by
  cases step <;> assumption

theorem lt_right (wf : nfa.WellFormed) (step : nfa.Step lb i it j it' update) : j < nfa.nodes.size := by
  have inBounds := wf.inBounds ⟨i, step.lt⟩
  cases step <;> simp_all [Node.inBounds]

theorem it_eq_or_next (step : nfa.Step lb i it j it' update) : it' = it ∨ (it.hasNext ∧ it' = it.next) := by
  cases step
  case char _ _ _ vf _ => simp [vf.hasNext]
  case sparse _ _ _ vf _ => simp [vf.hasNext]
  all_goals simp

theorem le_pos (step : nfa.Step lb i it j it' update) : it.pos ≤ it'.pos := by
  cases step.it_eq_or_next with
  | inl eq => exact eq ▸ Nat.le_refl _
  | inr eq =>
    simp only [Iterator.pos, eq, Iterator.next, String.Pos.Raw.next]
    exact Nat.le_add_right _ _

theorem validL (step : nfa.Step lb i it j it' update) : it.Valid := by
  cases step
  case char _ _ _ vf _ => exact vf.valid
  case sparse _ _ _ vf _ => exact vf.valid
  all_goals assumption

theorem validR (step : nfa.Step lb i it j it' update) : it'.Valid := by
  cases step
  case char _ _ _ vf _ => exact vf.next.valid
  case sparse _ _ _ vf _ => exact vf.next.valid
  all_goals assumption

theorem toString_eq (step : nfa.Step lb i it j it' update) :
  it'.toString = it.toString := by
  cases step.it_eq_or_next with
  | inl eq => simp [eq]
  | inr eq => simp [eq, String.Iterator.next, String.Pos.Raw.next]

theorem le_endPos (step : nfa.Step lb i it j it' update) : it'.pos ≤ it.toString.endPos :=
  step.toString_eq ▸ step.validR.le_endPos

theorem cast (step : nfa.Step lb i it j it' update)
  {lt : i < nfa'.nodes.size} (h : nfa[i]'step.lt = nfa'[i]) :
  nfa'.Step lb i it j it' update := by
  cases step with
  | epsilon ge _ eq v => exact .epsilon ge lt (h ▸ eq) v
  | anchor ge _ eq v h' => exact .anchor ge lt (h ▸ eq) v h'
  | splitLeft ge _ eq v => exact .splitLeft ge lt (h ▸ eq) v
  | splitRight ge _ eq v => exact .splitRight ge lt (h ▸ eq) v
  | save ge _ eq v => exact .save ge lt (h ▸ eq) v
  | char ge _ eq v => exact .char ge lt (h ▸ eq) v
  | sparse ge _ eq v mem => exact .sparse ge lt (h ▸ eq) v mem

theorem liftBound' (ge : lb' ≤ i) (step : nfa.Step lb i it j it' update) :
  nfa.Step lb' i it j it' update := by
  cases step with
  | epsilon _ lt eq v => exact .epsilon ge lt eq v
  | anchor _ lt eq h v => exact .anchor ge lt eq h v
  | splitLeft _ lt eq v => exact .splitLeft ge lt eq v
  | splitRight _ lt eq v => exact .splitRight ge lt eq v
  | save _ lt eq v => exact .save ge lt eq v
  | char _ lt eq v => exact .char ge lt eq v
  | sparse _ lt eq v mem => exact .sparse ge lt eq v mem

theorem liftBound (le : lb' ≤ lb) (step : nfa.Step lb i it j it' update) :
  nfa.Step lb' i it j it' update :=
  step.liftBound' (Nat.le_trans le step.ge)

theorem iff_done {lt : i < nfa.nodes.size} (eq : nfa[i] = .done) :
  nfa.Step lb i it j it' update ↔ False := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . simp

theorem iff_fail {lt : i < nfa.nodes.size} (eq : nfa[i] = .fail) :
  nfa.Step lb i it j it' update ↔ False := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . simp

theorem iff_epsilon {next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .epsilon next) :
  nfa.Step lb i it j it' update ↔ lb ≤ i ∧ j = next ∧ it' = it ∧ update = .none ∧ it.Valid := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hit, hupdate, v⟩
    simp_all
    exact .epsilon ge lt eq v

theorem iff_anchor {anchor next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .anchor anchor next) :
  nfa.Step lb i it j it' update ↔ lb ≤ i ∧ j = next ∧ it' = it ∧ update = .none ∧ it.Valid ∧ anchor.test it := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hit, hupdate, v, htest⟩
    simp_all
    exact .anchor ge lt eq v htest

theorem iff_split {next₁ next₂} {lt : i < nfa.nodes.size} (eq : nfa[i] = .split next₁ next₂) :
  nfa.Step lb i it j it' update ↔ lb ≤ i ∧ (j = next₁ ∨ j = next₂) ∧ it' = it ∧ update = .none ∧ it.Valid := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hit, hupdate, v⟩
    cases hj with
    | inl hj =>
      simp_all
      exact .splitLeft ge lt eq v
    | inr hj =>
      simp_all
      exact .splitRight ge lt eq v

theorem iff_save {offset next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .save offset next) :
  nfa.Step lb i it j it' update ↔ lb ≤ i ∧ j = next ∧ it' = it ∧ update = .some (offset, it.pos) ∧ it.Valid := by
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨ge, hj, hit, hupdate, v⟩
    simp_all
    exact .save ge lt eq v

theorem iff_char {c next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .char c next) :
  nfa.Step lb i it j it' update ↔ ∃ l r, lb ≤ i ∧ j = next ∧ it' = it.next ∧ update = .none ∧ it.ValidFor l (c :: r) := by
  apply Iff.intro
  . intro step
    cases step
    case char l c r ge lt vf v =>
      simp_all
      exact ⟨l, r, vf⟩
    all_goals simp_all
  . intro ⟨l, r, ge, hj, hit, hupdate, vf⟩
    simp_all
    exact .char ge lt eq vf

theorem iff_sparse {cs next} {lt : i < nfa.nodes.size} (eq : nfa[i] = .sparse cs next) :
  nfa.Step lb i it j it' update ↔ ∃ l c r, lb ≤ i ∧ j = next ∧ it' = it.next ∧ update = .none ∧ it.ValidFor l (c :: r) ∧ c ∈ cs := by
  apply Iff.intro
  . intro step
    cases step
    case sparse l c r cs ge lt mem vf hn =>
      simp [eq] at hn
      exact ⟨l, c, r, ge, by simp [hn.2], rfl, rfl, vf, hn.1 ▸ mem⟩
    all_goals simp_all
  . intro ⟨l, c, r, ge, hj, hit, hupdate, vf, mem⟩
    simp_all
    exact .sparse ge lt eq vf mem

theorem compile_liftBound {e nfa} (eq : compile e = nfa) (step : nfa.Step 0 i it j it' update) :
  nfa.Step 1 i it j it' update := by
  cases Nat.eq_zero_or_pos i with
  | inl eqi =>
    have lt : i < nfa.nodes.size := eqi ▸ lt_zero_size_compile eq
    have := (done_iff_zero_compile eq ⟨i, lt⟩).mpr eqi
    cases step <;> simp_all
  | inr gt => exact step.liftBound' gt

end Step

/--
A collection of steps in an NFA forms a path.
-/
inductive Path (nfa : NFA) (lb : Nat) : Nat → Iterator → Nat → Iterator → List (Nat × String.Pos.Raw) → Prop where
  | last {i it j it' update} (step : Step nfa lb i it j it' update) : Path nfa lb i it j it' (List.ofOption update)
  | more {i it j it' k it'' update updates} (step : Step nfa lb i it j it' update) (rest : Path nfa lb j it' k it'' updates) :
    Path nfa lb i it k it'' (update ::ₒ updates)

namespace Path

variable {nfa nfa' : NFA} {lb lb' i it j it' k it'' updates updates₁ updates₂}

theorem ge (path : nfa.Path lb i it j it' updates) : lb ≤ i := by
  cases path with
  | last step => exact step.ge
  | more step => exact step.ge

theorem lt (path : nfa.Path lb i it j it' updates) : i < nfa.nodes.size := by
  cases path with
  | last step => exact step.lt
  | more step => exact step.lt

theorem lt_right (wf : nfa.WellFormed) (path : nfa.Path lb i it j it' updates) : j < nfa.nodes.size := by
  induction path with
  | last step => exact step.lt_right wf
  | more _ _ ih => exact ih

theorem toString (path : nfa.Path lb i it j it' updates) : it'.toString = it.toString := by
  induction path with
  | last step => exact step.toString_eq
  | more step _ ih => exact step.toString_eq ▸ ih

theorem le_pos (path : nfa.Path lb i it j it' updates) : it.pos ≤ it'.pos := by
  induction path with
  | last step => exact step.le_pos
  | more step _ ih => exact Nat.le_trans step.le_pos ih

theorem validL (path : nfa.Path lb i it j it' updates) : it.Valid := by
  cases path with
  | last step => exact step.validL
  | more step => exact step.validL

theorem validR (path : nfa.Path lb i it j it' updates) : it'.Valid := by
  induction path with
  | last step => exact step.validR
  | more _ _ ih => exact ih

/--
A simpler casting procedure where the equality can be proven easily, e.g., when casting to a larger NFA.
-/
theorem cast (eq : ∀ i, lb ≤ i → (_ : i < nfa.nodes.size) → ∃ _ : i < nfa'.nodes.size, nfa[i] = nfa'[i])
  (path : nfa.Path lb i it j it' updates) :
  nfa'.Path lb i it j it' updates := by
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
  (path : nfa'.Path lb i it j it' updates) :
  nfa.Path lb i it j it' updates := by
  induction path with
  | last step => exact .last (step.cast (eq _ step.ge lt))
  | more step _ ih =>
    have step := step.cast (eq _ step.ge lt)
    have rest := ih (step.lt_right wf)
    exact .more step rest

theorem liftBound (le : lb' ≤ lb) (path : nfa.Path lb i it j it' updates) :
  nfa.Path lb' i it j it' updates := by
  induction path with
  | last step => exact .last (step.liftBound le)
  | more step _ ih => exact .more (step.liftBound le) ih

theorem liftBound' (ge : lb' ≤ i)
  (inv : ∀ {i it j it' update}, lb' ≤ i → lb ≤ j → nfa.Step lb i it j it' update → lb' ≤ j)
  (path : nfa.Path lb i it j it' updates) :
  nfa.Path lb' i it j it' updates := by
  induction path with
  | last step => exact .last (step.liftBound' ge)
  | more step rest ih => exact .more (step.liftBound' ge) (ih (inv ge rest.ge step))

theorem trans (path₁ : nfa.Path lb i it j it' updates₁) (path₂ : nfa.Path lb j it' k it'' updates₂) :
  nfa.Path lb i it k it'' (updates₁ ++ updates₂) := by
  induction path₁ with
  | last step =>
    simp
    exact .more step path₂
  | more step _ ih =>
    simp
    exact .more step (ih path₂)

theorem compile_liftBound {e nfa} (eq : compile e = nfa) (path : nfa.Path 0 i it j it' updates) :
  nfa.Path 1 i it j it' updates := by
  induction path with
  | last step => exact .last (step.compile_liftBound eq)
  | more step _ ih => exact .more (step.compile_liftBound eq) ih

/--
If a property is closed under a single step, then it is closed under a path.
-/
theorem of_step_closure {lb} (motive : Nat → Iterator → Prop) (closure : ∀ i it j it' update, motive i it → nfa.Step lb i it j it' update → motive j it')
  {i it j it' update} (base : motive i it) (path : nfa.Path lb i it j it' update) :
  motive j it' := by
  induction path with
  | @last i it j it' update step => exact closure i it j it' update base step
  | @more i it j it' k it'' update₁ _ step _ ih => exact ih (closure i it j it' update₁ base step)

end Path

end Regex.NFA
