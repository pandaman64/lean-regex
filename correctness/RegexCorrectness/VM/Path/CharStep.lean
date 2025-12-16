import RegexCorrectness.NFA.Semantics.Path

set_option autoImplicit false

open String (Pos)

namespace Regex.NFA

def CharStep {s : String} (nfa : NFA) (pos : Pos s) (i j : Fin nfa.nodes.size) : Prop :=
  ∃ ne : pos ≠ s.endPos, nfa.Step 0 i pos j (pos.next ne) .none

namespace CharStep

variable {s : String} {nfa : NFA} {pos : Pos s} {i j : Fin nfa.nodes.size}

@[grind →]
theorem ne (step : nfa.CharStep pos i j) : pos ≠ s.endPos := by
  grind [CharStep]

@[grind →]
theorem step (step : nfa.CharStep pos i j) :
  nfa.Step 0 i pos j (pos.next step.ne) .none := by
  grind [CharStep]

@[simp, grind =]
theorem done (hn : nfa[i] = .done) :
  nfa.CharStep pos i j ↔ False := by
  simp [CharStep, Step.iff_done hn]

@[simp, grind =]
theorem fail (hn : nfa[i] = .fail) :
  nfa.CharStep pos i j ↔ False := by
  simp [CharStep, Step.iff_fail hn]

@[simp, grind =>]
theorem epsilon {next} (hn : nfa[i] = .epsilon next) :
  nfa.CharStep pos i j ↔ False := by
  simp [CharStep, Step.iff_epsilon hn, pos.ne_next.symm]

@[simp, grind =>]
theorem anchor {anchor next} (hn : nfa[i] = .anchor anchor next) :
  nfa.CharStep pos i j ↔ False := by
  simp [CharStep, Step.iff_anchor hn, pos.ne_next.symm]

@[simp, grind =>]
theorem split {next₁ next₂} (hn : nfa[i] = .split next₁ next₂) :
  nfa.CharStep pos i j ↔ False := by
  simp [CharStep, Step.iff_split hn, pos.ne_next.symm]

@[simp, grind =>]
theorem save {offset next} (hn : nfa[i] = .save offset next) :
  nfa.CharStep pos i j ↔ False := by
  simp [CharStep, Step.iff_save hn]

@[simp, grind =>]
theorem char {c next} (hn : nfa[i] = .char c next) :
  nfa.CharStep pos i j ↔ ∃ ne : pos ≠ s.endPos, j = next ∧ pos.get ne = c := by
  simp [CharStep, Step.iff_char hn]

@[simp, grind =>]
theorem sparse {cs next} (hn : nfa[i] = .sparse cs next) :
  nfa.CharStep pos i j ↔ ∃ ne : pos ≠ s.endPos, j = next ∧ pos.get ne ∈ cs := by
  simp [CharStep, Step.iff_sparse hn]

@[grind .]
theorem char_or_sparse (step : nfa.CharStep pos i j) :
  (∃ c next, nfa[i] = .char c next) ∨ (∃ cs next, nfa[i] = .sparse cs next) := by
  grind [CharStep]

end CharStep

end Regex.NFA
