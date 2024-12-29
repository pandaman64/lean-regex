import RegexCorrectness.NFA.Semantics.Path
import RegexCorrectness.VM.Basic2

set_option autoImplicit false

open Regex.Data (Span)

namespace Regex.NFA

def CharStep (nfa : NFA) (l m : List Char) (c : Char) (r : List Char) (i j : Fin nfa.nodes.size) : Prop :=
  nfa.Step 0 i ⟨l, m, c :: r⟩ j ⟨l, c :: m, r⟩ .none

namespace CharStep

variable {nfa : NFA} {l m : List Char} {c : Char} {r : List Char} {i j : Fin nfa.nodes.size}

@[simp]
theorem done (hn : nfa[i] = .done) :
  nfa.CharStep l m c r i j ↔ False := by
  apply Step.iff_done hn

@[simp]
theorem fail (hn : nfa[i] = .fail) :
  nfa.CharStep l m c r i j ↔ False := by
  apply Step.iff_fail hn

@[simp]
theorem epsilon {next} (hn : nfa[i] = .epsilon next) :
  nfa.CharStep l m c r i j ↔ False := by
  simp [CharStep, Step.iff_epsilon hn]

@[simp]
theorem split {next₁ next₂} (hn : nfa[i] = .split next₁ next₂) :
  nfa.CharStep l m c r i j ↔ False := by
  simp [CharStep, Step.iff_split hn]

@[simp]
theorem save {offset next} (hn : nfa[i] = .save offset next) :
  nfa.CharStep l m c r i j ↔ False := by
  simp [CharStep, Step.iff_save hn]

@[simp]
theorem char {c' next} (hn : nfa[i] = .char c' next) :
  nfa.CharStep l m c r i j ↔ c = c' ∧ j = next := by
  simp [CharStep, Step.iff_char]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro eq
    simp [eq]
    exact Step.char (Nat.zero_le _) i.isLt hn

@[simp]
theorem sparse {cs next} (hn : nfa[i] = .sparse cs next) :
  nfa.CharStep l m c r i j ↔ c ∈ cs ∧ j = next := by
  rw [CharStep]
  apply Iff.intro
  . intro step
    cases step <;> simp_all
  . intro ⟨mem, eq⟩
    simp [eq]
    exact Step.sparse (Nat.zero_le _) i.isLt hn mem

theorem char_or_sparse (step : nfa.CharStep l m c r i j) :
  (∃ c' next, nfa[i] = .char c' next) ∨ (∃ cs next, nfa[i] = .sparse cs next) := by
  cases step <;> simp_all

theorem write_update (step : nfa.CharStep l m c r i j) : Regex.VM.WriteUpdate i := by
  cases step <;> simp_all [VM.WriteUpdate]

end CharStep

end Regex.NFA
