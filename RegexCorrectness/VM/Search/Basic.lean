import RegexCorrectness.VM.Path
import RegexCorrectness.VM.EpsilonClosure
import RegexCorrectness.VM.CharStep

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.VM

def captureNext' (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) : Option (List (Nat × Pos)) :=
  let updates : Vec (List (Nat × Pos)) nfa.nodes.size := Vec.ofFn (fun _ => [])
  let (matched, current) := εClosure' nfa wf it .none ⟨.empty, updates⟩ [([], ⟨nfa.start, wf.start_lt⟩)]
  go it matched current ⟨.empty, updates⟩
where
  go (it : Iterator) (matched : Option (List (Nat × Pos))) (current next : SearchState' nfa) :
    Option (List (Nat × String.Pos)) :=
    if it.atEnd then
      matched
    else
      if current.states.isEmpty && matched.isSome then
        matched
      else
        if matched.isNone then
          let expanded := εClosure' nfa wf it .none current [([], ⟨nfa.start, wf.start_lt⟩)]
          let stepped := eachStepChar' nfa wf it expanded.2 next
          go it.next stepped.1 stepped.2 ⟨current.states.clear, current.updates⟩
        else
          let stepped := eachStepChar' nfa wf it current next
          go it.next stepped.1 stepped.2 ⟨current.states.clear, current.updates⟩

theorem captureNext'.go.induct' (nfa : NFA) (wf : nfa.WellFormed)
  (motive : Iterator → Option (List (ℕ × Pos)) → SearchState' nfa → SearchState' nfa → Prop)
  (not_found : ∀ it matched current next,
    it.atEnd →
    motive it matched current next)
  (found : ∀ it matched current next,
    ¬it.atEnd → current.states.isEmpty → matched.isSome →
    motive it matched current next)
  (ind_not_found : ∀ it matched current next _matched current' matched' next',
    ¬it.atEnd → matched.isNone →
    εClosure' nfa wf it .none current [([], ⟨nfa.start, wf.start_lt⟩)] = (_matched, current') →
    eachStepChar' nfa wf it current' next = (matched', next') →
    motive it.next matched' next' ⟨current.states.clear, current.updates⟩ →
    motive it matched current next)
  (ind_found : ∀ it matched current next matched' next',
    ¬it.atEnd → ¬current.states.isEmpty → matched.isSome →
    eachStepChar' nfa wf it current next = (matched', next') →
    motive it.next matched' next' ⟨current.states.clear, current.updates⟩ →
    motive it matched current next)
  (it : Iterator) (matched : Option (List (ℕ × Pos))) (current next : SearchState' nfa) :
  motive it matched current next :=
  captureNext'.go.induct nfa wf motive
    (fun it matched current next atEnd => not_found it matched current next atEnd)
    (fun it matched current next atEnd h =>
      found it matched current next atEnd (by simp at h; exact h.1) (by simp at h; exact h.2))
    (fun it matched current next atEnd h isNone ih =>
      let expanded := εClosure' nfa wf it .none current [([], ⟨nfa.start, wf.start_lt⟩)]
      let stepped := eachStepChar' nfa wf it expanded.2 next
      ind_not_found it matched current next expanded.1 expanded.2 stepped.1 stepped.2
        atEnd isNone rfl rfl ih)
    (fun it matched current next atEnd h isSome ih =>
      let stepped := eachStepChar' nfa wf it current next
      ind_found it matched current next stepped.1 stepped.2
        atEnd (by simp at isSome; simp [isSome] at h; simp [h]) (by cases matched <;> simp at isSome; simp) rfl ih)
    it matched current next

end Regex.VM
