import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open String (Pos)

namespace Regex.VM

variable {s : String}

theorem captureNext.go.induct' (σ : Strategy s) (nfa : NFA) (wf : nfa.WellFormed)
  (motive : Pos s → Option σ.Update → SearchState σ nfa → SearchState σ nfa → Prop)
  (not_found : ∀ matched current next,
    motive s.endPos matched current next)
  (found : ∀ pos matched current next,
    pos ≠ s.endPos →
    current.states.isEmpty →
    matched.isSome →
    motive pos matched current next)
  (ind_not_found : ∀ pos matched current next ne,
    let stepped := eachStepChar σ nfa wf pos ne current next
    let expanded := εClosure σ nfa wf (pos.next ne) .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
    matched = .none →
    stepped.1 = .none →
    motive (pos.next ne) expanded.1 expanded.2 ⟨current.states.clear, current.updates⟩ →
    motive pos matched current next)
  (ind_found : ∀ pos matched current next ne,
    let stepped := eachStepChar σ nfa wf pos ne current next
    (matched.isSome → ¬current.states.isEmpty) →
    matched.isSome ∨ stepped.1.isSome →
    motive (pos.next ne) (stepped.1 <|> matched) stepped.2 ⟨current.states.clear, current.updates⟩ →
    motive pos matched current next)
  (pos : Pos s) (matched : Option σ.Update) (current next : SearchState σ nfa) :
  motive pos matched current next :=
  captureNext.go.induct σ nfa wf motive
    (fun matched current next => not_found matched current next)
    (fun pos matched current next ne h =>
      found pos matched current next ne (by grind) (by grind))
    (fun pos matched current next ne h₁ h₂ ih => by
      let stepped := eachStepChar σ nfa wf pos ne current next
      let expanded := εClosure σ nfa wf pos .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
      rw [Option.isNone_iff_eq_none, Option.orElse_eq_none] at h₂
      exact ind_not_found pos matched current next ne h₂.2 h₂.1 ih)
    (fun pos matched current next ne h₁ h₂ ih => by
      let stepped := eachStepChar σ nfa wf pos ne current next
      exact ind_found pos matched current next ne (by grind) (by grind [Option.isSome_iff_ne_none]) ih)
    pos matched current next

section

@[simp, grind =]
theorem captureNext.go_not_found {σ nfa wf matched current next} :
  captureNext.go σ nfa wf s.endPos matched current next = matched := by
  grind [captureNext.go]

@[simp, grind =]
theorem captureNext.go_found {σ nfa wf pos matched current next}
  (ne : pos ≠ s.endPos) (isEmpty : current.states.isEmpty) (isSome : matched.isSome) :
  captureNext.go σ nfa wf pos matched current next = matched := by
  grind [captureNext.go]

@[simp, grind =>]
theorem captureNext.go_ind_not_found {σ : Strategy s} {nfa wf pos matched current next ne} (stepped expanded)
  (eq₁ : stepped = eachStepChar σ nfa wf pos ne current next)
  (eq₂ : expanded = εClosure σ nfa wf (pos.next ne) .none stepped.2 [(σ.empty, ⟨nfa.start, wf.start_lt⟩)])
  (isNone₁ : matched = .none) (isNone₂ : stepped.1 = .none) :
  captureNext.go σ nfa wf pos matched current next =
  captureNext.go σ nfa wf (pos.next ne) expanded.1 expanded.2 ⟨current.states.clear, current.updates⟩ := by
  grind [captureNext.go]

@[simp, grind →]
theorem captureNext.go_ind_found {σ : Strategy s} {nfa wf pos matched current next ne} (stepped)
  (eq : stepped = eachStepChar σ nfa wf pos ne current next)
  (hemp : matched.isSome → ¬current.states.isEmpty) (isSome : matched.isSome ∨ stepped.1.isSome) :
  captureNext.go σ nfa wf pos matched current next =
  captureNext.go σ nfa wf (pos.next ne) (stepped.1 <|> matched) stepped.2 ⟨current.states.clear, current.updates⟩ := by
  grind [captureNext.go, Option.orElse_eq_orElse, Option.isNone_iff_eq_none]

end

end Regex.VM
