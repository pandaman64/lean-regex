import Regex.Regex
import Regex.NFA.Basic2

-- Port of https://github.com/desi-ivanov/agda-regexp-automata/blob/master/Regexp/RegexpNfa.agda

namespace Regex2.NFA

def empty : NFA 1 := {
  start := ⟨0, by decide⟩
  δ := fun _ _ => ∅
  final := ∅
}

def epsilon : NFA 1 := {
  start := ⟨0, by decide⟩
  δ := fun _ _ => ∅
  final := {⟨0, by decide⟩}
}

def char (c : Char) : NFA 2 := {
  start := ⟨0, by decide⟩
  δ := fun i c' => if i = 0 && c = c' then {⟨1, by decide⟩} else ∅
  final := {⟨1, by decide⟩}
}

theorem empty.correct : ¬ empty ⇓ cs := by
  cases cs <;> simp [empty, accepts]

theorem empty.correct' (cs) : Regex.empty.matches ⟨cs⟩ ↔ empty ⇓ cs :=
  ⟨fun h => (Regex.empty_not_matches h).elim, fun h => (empty.correct h).elim⟩

theorem epsilon.correct : epsilon ⇓ cs ↔ cs = [] := by
  cases cs <;> simp [epsilon, accepts]

theorem epsilon.correct' (cs) : Regex.epsilon.matches ⟨cs⟩ ↔ epsilon ⇓ cs :=
  have : ⟨cs⟩ = "" → cs = [] := by
    intro h
    apply String.noConfusion h
    intro h
    exact h
  ⟨fun h => epsilon.correct.mpr (this (Regex.epsilon_matches_only_empty _ h)),
  fun h => .epsilon (by simp [epsilon.correct.mp h])⟩

theorem char.correct {c : Char} : char c ⇓ cs ↔ cs = [c] := by
  cases cs with
  | nil => simp [char, accepts]
  | cons c' cs =>
    apply Iff.intro
    . simp [accepts]
      intro i step acc
      simp [char] at step
      split at step <;> try contradiction
      next h =>
        refine ⟨h.symm, ?_⟩
        cases cs with
        | nil => rfl
        | cons =>
          simp at step
          simp [accepts, step, char] at acc
    . simp
      intro h₁ h₂
      simp [h₁, h₂, accepts, char]

theorem char.correct' (cs) : (Regex.char c).matches ⟨cs⟩ ↔ char c ⇓ cs := by
  apply Iff.intro
  . intro m
    have eq := Regex.char_matches m
    apply String.noConfusion eq
    intro eq
    exact char.correct.mpr eq
  . simp
    intro acc
    have eq := char.correct.mp acc
    exact .char c (by simp [eq])

def compile : (r : Regex) → Σ n : Nat, { nfa : NFA n // ∀ cs, r.matches ⟨cs⟩ ↔ nfa ⇓ cs }
  | .empty => ⟨_, ⟨empty, empty.correct'⟩⟩
  | .epsilon => ⟨_, ⟨epsilon, epsilon.correct'⟩⟩
  | .char c => ⟨_, ⟨char c, char.correct'⟩⟩
  | .alternate r₁ r₂ =>
    let ⟨_, ⟨nfa₁, p₁⟩⟩ := compile r₁
    let ⟨_, ⟨nfa₂, p₂⟩⟩ := compile r₂
    let nfa := union nfa₁ nfa₂

    have correct (cs) : (Regex.alternate r₁ r₂).matches ⟨cs⟩ ↔ nfa ⇓ cs := by
      simp [Regex.alternate_matches_or]
      apply Iff.intro
      . intro m
        cases m with
        | inl m₁ => exact union_correct.mpr (.inl ((p₁ cs).mp m₁))
        | inr m₂ => exact union_correct.mpr (.inr ((p₂ cs).mp m₂))
      . intro acc
        cases union_correct.mp acc with
        | inl acc₁ => exact .inl ((p₁ cs).mpr acc₁)
        | inr acc₂ => exact .inr ((p₂ cs).mpr acc₂)

    ⟨_, ⟨nfa, correct⟩⟩
  | .concat r₁ r₂ =>
    let ⟨_, ⟨nfa₁, p₁⟩⟩ := compile r₁
    let ⟨_, ⟨nfa₂, p₂⟩⟩ := compile r₂
    let nfa := concat nfa₁ nfa₂

    have correct (cs) : (Regex.concat r₁ r₂).matches ⟨cs⟩ ↔ nfa ⇓ cs := by
      simp [Regex.concat_matches]
      apply Iff.intro
      . intro m
        let ⟨s₁, s₂, eqs, m₁, m₂⟩ := m
        have acc₁ := (p₁ s₁.data).mp m₁
        have acc₂ := (p₂ s₂.data).mp m₂
        have : cs = s₁.data ++ s₂.data := by
          apply String.noConfusion eqs
          intro h
          exact h
        exact concat_correct.mpr ⟨s₁.data, s₂.data, this, acc₁, acc₂⟩
      . intro acc
        let ⟨cs₁, cs₂, eqs, acc₁, acc₂⟩ := concat_correct.mp acc
        have m₁ := (p₁ cs₁).mpr acc₁
        have m₂ := (p₂ cs₂).mpr acc₂
        have : String.mk cs = ⟨cs₁⟩ ++ ⟨cs₂⟩ := by
          simp [eqs]
          rfl
        exact ⟨⟨cs₁⟩, ⟨cs₂⟩, this, m₁, m₂⟩

    ⟨_, ⟨nfa, correct⟩⟩
  | .star r =>
    let ⟨_, ⟨nfa, p⟩⟩ := compile r
    let nfa' := star nfa

    have correct₁ {s} (m : (Regex.star r).matches s) : nfa' ⇓ s.data := by
      generalize h : Regex.star r = r'
      rw [h] at m
      simp
      induction m with
      | epsilon | char | alternateLeft | alternateRight | concat => contradiction
      | starEpsilon eqs => simp [eqs, accepts, star]
      | starConcat s s₁ s₂ r eqs m₁ m₂ _ ih₂ =>
        apply Regex.noConfusion h
        intro eqr
        subst eqr
        have acc₁ := (p s₁.data).mp m₁
        have acc₂ := ih₂ rfl
        exact eqs ▸ star_correct₁ acc₁ acc₂

    let rec correct₂ {cs} (acc : nfa' ⇓ cs) : (Regex.star r).matches ⟨cs⟩ := by
      cases cs with
      | nil => exact .starEpsilon rfl
      | cons c cs =>
        let ⟨cs₁, cs₂, eqs, acc₁, acc₂⟩ := star_correct₂ acc
        have m₁ := (p (c :: cs₁)).mpr acc₁
        have m₂ := correct₂ acc₂
        have m := Regex.matches.starConcat ⟨c :: cs₁ ++ cs₂⟩ ⟨c :: cs₁⟩ ⟨cs₂⟩ r rfl m₁ m₂
        exact eqs.symm ▸ m

    have correct (cs) : (Regex.star r).matches ⟨cs⟩ ↔ nfa' ⇓ cs := ⟨correct₁, correct₂⟩

    ⟨_, ⟨nfa', correct⟩⟩
termination_by correct₂ _ => cs.length

end Regex2.NFA
