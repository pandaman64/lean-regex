import RegexCorrectness.VM.Search
import RegexCorrectness.Strategy

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.Strategy (materializeUpdates)
open String (Iterator)
open String.Pos (Raw)

/-
The correctness proofs use the refined versions of the VM functions to track all updates to the
capture groups while the actual implementation tracks only the last update per capture group.

This files estabilishes the correspondence between the refined and actual VM functions.
-/
namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {bufferSize : Nat} {it : Iterator}
  {matchedH : Option (List (Nat × Raw))} {matchedB : Option (Buffer bufferSize)}
  {nextH : SearchState HistoryStrategy nfa} {nextB : SearchState (BufferStrategy bufferSize) nfa}
  {stackH : εStack HistoryStrategy nfa} {stackB : εStack (BufferStrategy bufferSize) nfa}

def SearchState.materialize (stateH : SearchState HistoryStrategy nfa) : SearchState (BufferStrategy bufferSize) nfa :=
  ⟨stateH.states, stateH.updates.map (materializeUpdates bufferSize)⟩

@[simp]
theorem SearchState.materialize_states {stateH : SearchState HistoryStrategy nfa} :
  (stateH.materialize (bufferSize := bufferSize)).states = stateH.states := rfl

def εStack.materialize (stackH : εStack HistoryStrategy nfa) : εStack (BufferStrategy bufferSize) nfa :=
  stackH.map (fun (update, state) => (materializeUpdates bufferSize update, state))

@[simp]
theorem εStack.materialize.nil : εStack.materialize [] = ([] : εStack (BufferStrategy bufferSize) nfa) := rfl

@[simp]
theorem εStack.materialize.cons {entry} :
  εStack.materialize (entry :: stackH) = (materializeUpdates bufferSize entry.1, entry.2) :: εStack.materialize stackH := rfl

def materializeResult (resultH : Option HistoryStrategy.Update × SearchState HistoryStrategy nfa) : Option (BufferStrategy bufferSize).Update × SearchState (BufferStrategy bufferSize) nfa :=
  ⟨resultH.1.map (materializeUpdates bufferSize), resultH.2.materialize⟩

theorem εClosure.pushNext.refines {state : Fin nfa.nodes.size} {update} {buffer} (wf : nfa.WellFormed)
  (h₁ : materializeUpdates bufferSize update = buffer) (h₂ : εStack.materialize stackH = stackB) :
  εStack.materialize (pushNext HistoryStrategy nfa it nfa[state] (wf.inBounds' state rfl) update stackH)
    = (pushNext (BufferStrategy bufferSize) nfa it nfa[state] (wf.inBounds' state rfl) buffer stackB) := by
  cases nfa[state], wf.inBounds' state rfl, update, stackH using pushNext.fun_cases' HistoryStrategy nfa it with
  | epsilon _ _ state' inBounds => simp only [pushNext.epsilon rfl, εStack.materialize.cons, h₁, h₂]
  | split _ _ state₁ state₂ inBounds => simp only [pushNext.split rfl, εStack.materialize.cons, h₁, h₂]
  | save _ _ offset state' inBounds =>
    simp only [pushNext.save rfl, εStack.materialize.cons]
    simp [h₁, h₂]
  | anchor_pos _ _ a state' inBounds ht => simp only [pushNext.anchor_pos rfl ht, εStack.materialize.cons, h₁, h₂]
  | anchor_neg _ _ a state' inBounds ht => simp [pushNext.anchor_neg rfl ht, h₂]
  | done => simp [pushNext.done, h₂]
  | fail => simp [pushNext.fail, h₂]
  | char => simp [pushNext.char rfl, h₂]
  | sparse => simp [pushNext.sparse rfl, h₂]

theorem εClosure.refines (resultB resultH)
  (h : εClosure (BufferStrategy bufferSize) nfa wf it matchedB nextB stackB = resultB)
  (h' : εClosure HistoryStrategy nfa wf it matchedH nextH stackH = resultH)
  (refMatched : matchedH.map (materializeUpdates bufferSize) = matchedB)
  (refState : nextH.materialize = nextB)
  (refStack : stackH.materialize = stackB) :
  materializeResult resultH = resultB := by
  induction matchedH, nextH, stackH using εClosure.induct' HistoryStrategy nfa wf it generalizing matchedB nextB stackB resultB resultH with
  | base matchedH nextH =>
    simp [εStack.materialize] at refStack
    subst stackB
    rw [εClosure.base] at h' h
    simp [←h', ←h, materializeResult, refMatched, refState]
  | visited matched' next' update state' stack' mem ih =>
    simp only [εStack.materialize.cons] at refStack
    subst stackB
    rw [εClosure.visited mem] at h'
    rw [εClosure.visited (refState ▸ mem)] at h
    exact ih resultB resultH h h' refMatched refState rfl
  | not_visited matched' next' update state' stack' mem node =>
    rename_i matched'' states'' updates'' ih
    simp only [εStack.materialize.cons] at refStack
    subst stackB
    rw [εClosure.not_visited mem] at h'
    rw [εClosure.not_visited (refState ▸ mem)] at h
    refine ih resultB resultH h h' ?_ ?_ ?_
    . split
      next eq => simp [matched'', node, eq, ←refMatched]
      next eq =>
        simp at eq
        simp [matched'', node, eq, refMatched]
    . simp [SearchState.materialize] at refState
      simp [SearchState.materialize, states'', ←refState]
      split <;> simp [updates'', node, *]
    . exact pushNext.refines wf rfl rfl

theorem stepChar.refines {currentUpdatesH currentUpdatesB state} (resultB resultH)
  (h : stepChar (BufferStrategy bufferSize) nfa wf it currentUpdatesB nextB state = resultB)
  (h' : stepChar HistoryStrategy nfa wf it currentUpdatesH nextH state = resultH)
  (refUpdates : currentUpdatesH.map (materializeUpdates bufferSize) = currentUpdatesB)
  (refState : nextH.materialize = nextB) :
  materializeResult resultH = resultB := by
  simp [stepChar] at h h'
  split at h'
  next state' hn =>
    simp [hn] at h
    exact εClosure.refines resultB resultH h h' rfl refState (by simp [εStack.materialize, ←refUpdates])
  next hn =>
    simp [hn] at h
    simpa [←h', ←h, materializeResult] using refState

theorem eachStepChar.go.refines {currentH currentB i hleB hleH} (resultB resultH)
  (h : eachStepChar.go (BufferStrategy bufferSize) nfa wf it currentB i hleB nextB = resultB)
  (h' : eachStepChar.go HistoryStrategy nfa wf it currentH i hleH nextH = resultH)
  (refCurrent : currentH.materialize = currentB)
  (refNext : nextH.materialize = nextB) :
  materializeResult resultH = resultB := by
  induction i, hleH, nextH using eachStepChar.go.induct' HistoryStrategy nfa wf it generalizing currentB nextB resultB resultH with
  | base nextH =>
    simp at h'
    simp [←refCurrent] at h
    have eqi : currentH.states.count = (currentH.materialize (bufferSize := bufferSize)).states.count := by
      simp
    simp [←h', ←h, eqi, ←refNext, materializeResult]
  | done i hltH nextH hnH =>
    have hltB : i < currentB.states.count := by
      simpa [←refCurrent] using hltH
    have hnB : nfa[currentB.states[i]] = .done := by
      simpa [←refCurrent] using hnH
    simp [eachStepChar.go_done hltH hnH] at h'
    simp [eachStepChar.go_done hltB hnB] at h
    simp [←h', ←h, ←refNext, materializeResult]
  | found i hltH nextH hnH matchedH nextH' hstepH isSomeH =>
    have hltB : i < currentB.states.count := by
      simpa [←refCurrent] using hltH
    have hnB : nfa[currentB.states[i]] ≠ .done := by
      simpa [←refCurrent] using hnH
    have eqState : currentB.states[i] = currentH.states[i] := by
      simp [←refCurrent]
    have refUpdates : Vector.map (materializeUpdates bufferSize) currentH.updates = currentB.updates := by
      simp [←refCurrent, SearchState.materialize]

    let (eq := hstepB) (matchedB, nextB') := stepChar (BufferStrategy bufferSize) nfa wf it currentB.updates nextB currentB.states[i]
    have refResult := stepChar.refines (matchedB, nextB') (matchedH, nextH') hstepB (eqState ▸ hstepH) refUpdates refNext
    simp [materializeResult] at refResult

    have isSomeB : matchedB.isSome := by
      simpa [←refResult.1] using isSomeH

    simp [eachStepChar.go_found hltH hnH hstepH isSomeH] at h'
    simp [eachStepChar.go_found hltB hnB hstepB isSomeB] at h
    simpa [←h', ←h, materializeResult] using refResult
  | not_found i hltH nextH hnH matchedH nextH' hstepH isSomeH ih =>
    have hltB : i < currentB.states.count := by
      simpa [←refCurrent] using hltH
    have hnB : nfa[currentB.states[i]] ≠ .done := by
      simpa [←refCurrent] using hnH
    have eqState : currentB.states[i] = currentH.states[i] := by
      simp [←refCurrent]
    have refUpdates : Vector.map (materializeUpdates bufferSize) currentH.updates = currentB.updates := by
      simp [←refCurrent, SearchState.materialize]

    let (eq := hstepB) (matchedB, nextB') := stepChar (BufferStrategy bufferSize) nfa wf it currentB.updates nextB currentB.states[i]
    have refResult := stepChar.refines (matchedB, nextB') (matchedH, nextH') hstepB (eqState ▸ hstepH) refUpdates refNext
    simp [materializeResult] at refResult

    have isSomeB : ¬matchedB.isSome := by
      simpa [←refResult.1] using isSomeH

    simp [eachStepChar.go_not_found hltH hnH hstepH isSomeH] at h'
    simp [eachStepChar.go_not_found hltB hnB hstepB isSomeB] at h
    exact ih resultB resultH h h' refCurrent refResult.2

theorem eachStepChar.refines {currentH currentB} (resultB resultH)
  (h : eachStepChar (BufferStrategy bufferSize) nfa wf it currentB nextB = resultB)
  (h' : eachStepChar HistoryStrategy nfa wf it currentH nextH = resultH)
  (refCurrent : currentH.materialize = currentB)
  (refNext : nextH.materialize = nextB) :
  materializeResult resultH = resultB :=
  eachStepChar.go.refines resultB resultH h h' refCurrent refNext

theorem captureNext.go.refines {currentH currentB resultB resultH}
  (h : captureNext.go (BufferStrategy bufferSize) nfa wf it matchedB currentB nextB = resultB)
  (h' : captureNext.go HistoryStrategy nfa wf it matchedH currentH nextH = resultH)
  (refMatched : matchedH.map (materializeUpdates bufferSize) = matchedB)
  (refCurrent : currentH.materialize = currentB)
  (refNext : nextH.materialize = nextB) :
  resultH.map (materializeUpdates bufferSize) = resultB := by
  induction it, matchedH, currentH, nextH using captureNext.go.induct' HistoryStrategy nfa wf generalizing matchedB currentB nextB resultB resultH with
  | not_found it matched' current' next' atEnd =>
    rw [captureNext.go_not_found atEnd] at h'
    rw [captureNext.go_not_found atEnd] at h
    simp [←h', ←h, refMatched]
  | found it matchedH currentH nextH atEnd isEmptyH isSomeH =>
    have isEmptyB : currentB.states.isEmpty := by
      simpa [←refCurrent] using isEmptyH
    have isSomeB : matchedB.isSome := by
      simpa [←refMatched] using isSomeH
    rw [captureNext.go_found atEnd isEmptyH isSomeH] at h'
    rw [captureNext.go_found atEnd isEmptyB isSomeB] at h
    simp [←h', ←h, refMatched]
  | ind_not_found it matchedH currentH nextH steppedH expandedH atEnd isNoneH₁ =>
    rename_i isNoneH₂ ih
    let steppedB := eachStepChar (BufferStrategy bufferSize) nfa wf it currentB nextB
    let expandedB := εClosure (BufferStrategy bufferSize) nfa wf it.next .none steppedB.2 [(Buffer.empty, ⟨nfa.start, wf.start_lt⟩)]

    have refStepped := eachStepChar.refines steppedB steppedH rfl rfl refCurrent refNext
    have refExpanded := εClosure.refines expandedB expandedH rfl rfl rfl (by simp [←refStepped, materializeResult]) rfl
    have isNoneB₁ : matchedB = .none := by
      simpa [←refMatched] using isNoneH₁
    have isNoneB₂ : steppedB.1 = .none := by
      simpa [←refStepped, materializeResult] using isNoneH₂

    rw [captureNext.go_ind_not_found steppedH expandedH rfl rfl atEnd isNoneH₁ isNoneH₂] at h'
    rw [captureNext.go_ind_not_found steppedB expandedB rfl rfl atEnd isNoneB₁ isNoneB₂] at h
    exact ih h h' (by simp [←refExpanded, materializeResult]) (by simp [←refExpanded, materializeResult]) (by simp [SearchState.materialize, ←refCurrent])
  | ind_found it matchedH currentH nextH steppedH atEnd hempH isSomeH =>
    rename_i ih
    let steppedB : Option (Buffer bufferSize) × SearchState (BufferStrategy bufferSize) nfa :=
      eachStepChar (BufferStrategy bufferSize) nfa wf it currentB nextB

    have refStepped := eachStepChar.refines steppedB steppedH rfl rfl refCurrent refNext
    have refMatched' :  (steppedH.1 <|> matchedH).map (materializeUpdates bufferSize) = (steppedB.1 <|> matchedB) := by
      simp [←refStepped, ←refMatched, materializeResult, Option.map_or]

    have hempB (h : matchedB.isSome) : ¬currentB.states.isEmpty := by
      simp [←refMatched] at h
      exact refCurrent ▸ hempH h
    have isSomeB : matchedB.isSome ∨ steppedB.1.isSome := by
      simpa [←refMatched, ←refStepped, materializeResult] using isSomeH

    rw [captureNext.go_ind_found steppedH rfl atEnd hempH isSomeH] at h'
    rw [captureNext.go_ind_found steppedB rfl atEnd hempB isSomeB] at h
    exact ih h h' refMatched' (by simp [←refStepped, materializeResult]) (by simp [SearchState.materialize, ←refCurrent])

theorem captureNext.refines :
  (captureNext HistoryStrategy nfa wf it).map (materializeUpdates bufferSize) = (captureNext (BufferStrategy bufferSize) nfa wf it) := by
  unfold captureNext
  simp
  generalize hexpandH : εClosure HistoryStrategy nfa wf it .none ⟨.empty, Vector.replicate nfa.nodes.size []⟩ [([], ⟨nfa.start, wf.start_lt⟩)] = expandedH
  generalize hexpandB : εClosure (BufferStrategy bufferSize) nfa wf it .none ⟨.empty, Vector.replicate nfa.nodes.size Buffer.empty⟩ [(Buffer.empty, ⟨nfa.start, wf.start_lt⟩)] = expandedB

  have refExpanded := εClosure.refines expandedB expandedH hexpandB hexpandH rfl (by simp [SearchState.materialize, Buffer.empty]) rfl
  exact captureNext.go.refines rfl rfl (by simp [←refExpanded, materializeResult]) (by simp [←refExpanded, materializeResult]) (by simp [SearchState.materialize, Buffer.empty])

end Regex.VM
