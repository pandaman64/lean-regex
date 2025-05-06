import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

theorem captureNext.go.induct' (σ : Strategy) (nfa : NFA) (wf : nfa.WellFormed)
  (motive : Iterator → Option σ.Update → SearchState σ nfa → SearchState σ nfa → Prop)
  (not_found : ∀ it matched current next,
    it.atEnd →
    motive it matched current next)
  (found : ∀ it matched current next,
    ¬it.atEnd →
    current.states.isEmpty →
    matched.isSome →
    motive it matched current next)
  (ind_not_found : ∀ it matched current next,
    let stepped := eachStepChar σ nfa wf it current next
    let expanded := εClosure σ nfa wf it.next .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
    ¬it.atEnd →
    matched = .none →
    stepped.1 = .none →
    motive it.next expanded.1 expanded.2 ⟨current.states.clear, current.updates⟩ →
    motive it matched current next)
  (ind_found : ∀ it matched current next,
    let stepped := eachStepChar σ nfa wf it current next
    ¬it.atEnd →
    (matched.isSome → ¬current.states.isEmpty) →
    matched.isSome ∨ stepped.1.isSome →
    motive it.next (stepped.1 <|> matched) stepped.2 ⟨current.states.clear, current.updates⟩ →
    motive it matched current next)
  (it : Iterator) (matched : Option σ.Update) (current next : SearchState σ nfa) :
  motive it matched current next :=
  captureNext.go.induct σ nfa wf motive
    (fun it matched current next atEnd => not_found it matched current next atEnd)
    (fun it matched current next atEnd h =>
      found it matched current next atEnd (by simp at h; exact h.1) (by simp at h; exact h.2))
    (fun it matched current next atEnd h₁ h₂ ih => by
      let stepped := eachStepChar σ nfa wf it current next
      let expanded := εClosure σ nfa wf it .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
      rw [Option.isNone_iff_eq_none, Option.orElse_eq_none] at h₂
      exact ind_not_found it matched current next atEnd h₂.2 h₂.1 ih)
    (fun it matched current next atEnd h₁ h₂ ih => by
      let stepped := eachStepChar σ nfa wf it current next
      rw [Bool.and_comm] at h₁
      simp at h₁
      have h₂' : matched.isSome ∨ stepped.1.isSome := by
        match matched with
        | .none =>
          simp only [Option.orElse_none, Option.isNone_iff_eq_none, ←Option.not_isSome_iff_eq_none, Decidable.not_not] at h₂
          exact .inr h₂
        | .some _ => exact .inl (by simp)
      exact ind_found it matched current next atEnd (by simpa using h₁) h₂' ih)
    it matched current next

section

@[simp]
theorem captureNext.go_not_found {σ nfa wf it matched current next} (atEnd : it.atEnd) :
  captureNext.go σ nfa wf it matched current next = matched := by
  simp [captureNext.go, atEnd]

@[simp]
theorem captureNext.go_found {σ nfa wf it matched current next}
  (atEnd : ¬it.atEnd) (isEmpty : current.states.isEmpty) (isSome : matched.isSome) :
  captureNext.go σ nfa wf it matched current next = matched := by
  simp [captureNext.go, atEnd, isEmpty, isSome]

@[simp]
theorem captureNext.go_ind_not_found {σ nfa wf it matched current next} (stepped expanded)
  (eq₁ : stepped = eachStepChar σ nfa wf it current next)
  (eq₂ : expanded = εClosure σ nfa wf it.next .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)])
  (atEnd : ¬it.atEnd) (isNone₁ : matched = .none) (isNone₂ : stepped.1 = .none) :
  captureNext.go σ nfa wf it matched current next =
  captureNext.go σ nfa wf it.next expanded.1 expanded.2 ⟨current.states.clear, current.updates⟩ := by
  conv =>
    lhs
    unfold captureNext.go
    simp [atEnd, isNone₁, isNone₂, ←eq₁, ←eq₂]

@[simp]
theorem captureNext.go_ind_found {σ nfa wf it matched current next} (stepped)
  (eq : stepped = eachStepChar σ nfa wf it current next)
  (atEnd : ¬it.atEnd) (hemp : matched.isSome → ¬current.states.isEmpty) (isSome : matched.isSome ∨ stepped.1.isSome) :
  captureNext.go σ nfa wf it matched current next =
  captureNext.go σ nfa wf it.next (stepped.1 <|> matched) stepped.2 ⟨current.states.clear, current.updates⟩ := by
  have h' : (current.states.isEmpty && matched.isSome) = false := by
    rw [Bool.and_comm]
    simpa using hemp
  have h'' : (stepped.1 <|> matched).isNone = false := by
    simp [Option.isSome_iff_ne_none]
    intro eq₁ eq₂
    simp [eq₁, eq₂] at isSome
  conv =>
    lhs
    unfold captureNext.go
    simp [atEnd, h', h'', ←eq]

end

end Regex.VM
