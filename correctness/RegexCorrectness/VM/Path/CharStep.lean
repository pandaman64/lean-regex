import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open String (Iterator)

namespace Regex.NFA

def CharStep (nfa : NFA) (it : Iterator) (i j : Fin nfa.nodes.size) : Prop :=
  nfa.Step 0 i it j it.next .none

namespace CharStep

variable {nfa : NFA} {it : Iterator} {i j : Fin nfa.nodes.size}

@[simp]
theorem done (hn : nfa[i] = .done) :
  nfa.CharStep it i j ↔ False := by
  apply Step.iff_done hn

@[simp]
theorem fail (hn : nfa[i] = .fail) :
  nfa.CharStep it i j ↔ False := by
  apply Step.iff_fail hn

@[simp]
theorem epsilon {next} (hn : nfa[i] = .epsilon next) :
  nfa.CharStep it i j ↔ False := by
  simp [CharStep, Step.iff_epsilon hn]

@[simp]
theorem anchor {anchor next} (hn : nfa[i] = .anchor anchor next) :
  nfa.CharStep it i j ↔ False := by
  simp [CharStep, Step.iff_anchor hn]

@[simp]
theorem split {next₁ next₂} (hn : nfa[i] = .split next₁ next₂) :
  nfa.CharStep it i j ↔ False := by
  simp [CharStep, Step.iff_split hn]

@[simp]
theorem save {offset next} (hn : nfa[i] = .save offset next) :
  nfa.CharStep it i j ↔ False := by
  simp [CharStep, Step.iff_save hn]

@[simp]
theorem char {c next} (hn : nfa[i] = .char c next) :
  nfa.CharStep it i j ↔ ∃ l r, j = next ∧ it.ValidFor l (c :: r) := by
  simp [CharStep, Step.iff_char hn]

@[simp]
theorem sparse {cs next} (hn : nfa[i] = .sparse cs next) :
  nfa.CharStep it i j ↔ ∃ l c r, j = next ∧ it.ValidFor l (c :: r) ∧ c ∈ cs := by
  simp [CharStep, Step.iff_sparse hn]

theorem char_or_sparse (step : nfa.CharStep it i j) :
  (∃ c next, nfa[i] = .char c next) ∨ (∃ cs next, nfa[i] = .sparse cs next) := by
  match hn : nfa[i] with
  | .char c next => simp
  | .sparse cs next => simp
  | .done | .fail | .epsilon _ => simp_all
  | .anchor _ _ => simp [anchor hn] at step
  | .split _ _ => simp [split hn] at step
  | .save _ _ => simp [save hn] at step

end CharStep

end Regex.NFA
