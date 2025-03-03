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
    ¬it.atEnd → current.states.isEmpty → matched.isSome →
    motive it matched current next)
  (ind_not_found : ∀ it matched current next _matched current' matched' next',
    ¬it.atEnd → matched.isNone →
    εClosure σ nfa wf it .none current [(σ.empty, ⟨nfa.start, wf.start_lt⟩)] = (_matched, current') →
    eachStepChar σ nfa wf it current' next = (matched', next') →
    motive it.next matched' next' ⟨current'.states.clear, current'.updates⟩ →
    motive it matched current next)
  (ind_found : ∀ it matched current next matched' next',
    ¬it.atEnd → ¬current.states.isEmpty → matched.isSome →
    eachStepChar σ nfa wf it current next = (matched', next') →
    motive it.next (matched' <|> matched) next' ⟨current.states.clear, current.updates⟩ →
    motive it matched current next)
  (it : Iterator) (matched : Option σ.Update) (current next : SearchState σ nfa) :
  motive it matched current next :=
  captureNext.go.induct σ nfa wf motive
    (fun it matched current next atEnd => not_found it matched current next atEnd)
    (fun it matched current next atEnd h =>
      found it matched current next atEnd (by simp at h; exact h.1) (by simp at h; exact h.2))
    (fun it matched current next atEnd h isNone ih =>
      let expanded := εClosure σ nfa wf it .none current [(σ.empty, ⟨nfa.start, wf.start_lt⟩)]
      let stepped := eachStepChar σ nfa wf it expanded.2 next
      ind_not_found it matched current next expanded.1 expanded.2 stepped.1 stepped.2
        atEnd isNone rfl rfl ih)
    (fun it matched current next atEnd h isSome ih =>
      let stepped := eachStepChar σ nfa wf it current next
      ind_found it matched current next stepped.1 stepped.2
        atEnd (by simp at isSome; simp [isSome] at h; simp [h]) (by cases matched <;> simp at isSome; simp) rfl ih)
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
theorem captureNext.go_ind_not_found {σ nfa wf it matched current next _matched current' matched' next'}
  (atEnd : ¬it.atEnd) (isNone : matched.isNone)
  (h₁ : εClosure σ nfa wf it .none current [(σ.empty, ⟨nfa.start, wf.start_lt⟩)] = (_matched, current'))
  (h₂ : eachStepChar σ nfa wf it current' next = (matched', next')) :
  captureNext.go σ nfa wf it matched current next = captureNext.go σ nfa wf it.next matched' next' ⟨current'.states.clear, current'.updates⟩ := by
  have isSome : ¬matched.isSome := by
    cases matched <;> simp_all
  conv =>
    lhs
    unfold captureNext.go
    simp [atEnd, isSome, isNone, h₁, h₂]

@[simp]
theorem captureNext.go_ind_found {σ nfa wf it matched current next matched' next'}
  (atEnd : ¬it.atEnd) (isEmpty : ¬current.states.isEmpty) (isSome : matched.isSome)
  (h : eachStepChar σ nfa wf it current next = (matched', next')) :
  captureNext.go σ nfa wf it matched current next = captureNext.go σ nfa wf it.next (matched' <|> matched) next' ⟨current.states.clear, current.updates⟩ := by
  have isNone : ¬matched.isNone := by
    cases matched <;> simp_all
  conv =>
    lhs
    unfold captureNext.go
    simp [atEnd, isEmpty, isSome, isNone, h]

end

end Regex.VM
