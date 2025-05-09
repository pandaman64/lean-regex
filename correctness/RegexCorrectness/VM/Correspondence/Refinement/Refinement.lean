import RegexCorrectness.VM.Search
import RegexCorrectness.Strategy.Refinement

set_option autoImplicit false

open Regex.Data (SparseSet)
open Regex (NFA)
open Regex.Strategy (refineUpdateOpt refineUpdates materializeUpdates)
open String (Pos Iterator)

/-
The correctness proofs use the refined versions of the VM functions to track all updates to the
capture groups while the actual implementation tracks only the last update per capture group.

This files estabilishes the correspondence between the refined and actual VM functions.
-/
namespace Regex.VM

variable {nfa : NFA} {wf : nfa.WellFormed} {bufferSize : Nat} {it : Iterator}
  {matched : Option (Buffer bufferSize)} {matched' : Option (List (Nat × Pos))}
  {next : SearchState (BufferStrategy bufferSize) nfa} {next' : SearchState HistoryStrategy nfa}
  {stack : εStack (BufferStrategy bufferSize) nfa} {stack' : εStack HistoryStrategy nfa}

def SearchState.refines (state' : SearchState HistoryStrategy nfa) (state : SearchState (BufferStrategy bufferSize) nfa) : Prop :=
  state'.states = state.states ∧ refineUpdates state'.updates state.updates

inductive εStack.refines : εStack HistoryStrategy nfa → εStack (BufferStrategy bufferSize) nfa → Prop where
  | nil : εStack.refines [] []
  | cons {update state' tail' buffer state tail}
    (h₁ : materializeUpdates bufferSize update = buffer) (h₂ : state' = state) (rest : εStack.refines tail' tail) :
    εStack.refines ((update, state') :: tail') ((buffer, state) :: tail)

@[simp]
theorem εStack.refines_nil : εStack.refines [] stack ↔ stack = [] :=
  ⟨fun ref => by cases ref; simp, fun h => h ▸ .nil⟩

@[simp]
theorem εStack.refines_cons {update state' tail' stack} :
  @εStack.refines nfa bufferSize ((update, state') :: tail') stack ↔
  ∃ buffer state tail, stack = (buffer, state) :: tail ∧ materializeUpdates bufferSize update = buffer ∧ state' = state ∧ @εStack.refines nfa bufferSize tail' tail := by
  apply Iff.intro
  . intro ref
    cases ref with
    | cons h₁ h₂ rest => exact ⟨_, _, _, rfl, h₁, h₂, rest⟩
  . intro ⟨buffer, state, tail, eq, h₁, h₂, rest⟩
    exact eq ▸ .cons h₁ h₂ rest

theorem εClosure.pushNext.refines {state : Fin nfa.nodes.size} {update} {buffer} (wf : nfa.WellFormed)
  (h₁ : materializeUpdates bufferSize update = buffer) (h₂ : εStack.refines stack' stack) :
  εStack.refines
    (pushNext HistoryStrategy nfa it nfa[state] (wf.inBounds' state rfl) update stack')
    (pushNext (BufferStrategy bufferSize) nfa it nfa[state] (wf.inBounds' state rfl) buffer stack) := by
  cases nfa[state], wf.inBounds' state rfl, update, stack' using pushNext.fun_cases' HistoryStrategy nfa it with
  | epsilon _ _ state' inBounds => simp [pushNext.epsilon rfl, h₁, h₂]
  | split _ _ state₁ state₂ inBounds => simp [pushNext.split rfl, h₁, h₂]
  | save _ _ offset state' inBounds =>
    simp [pushNext.save rfl, h₂]
    simp [HistoryStrategy, BufferStrategy, h₁]
  | anchor_pos _ _ a state' inBounds ht => simp [pushNext.anchor_pos rfl ht, h₁, h₂]
  | anchor_neg _ _ a state' inBounds ht => simp [pushNext.anchor_neg rfl ht, h₁, h₂]
  | done => simp [pushNext.done, h₁, h₂]
  | fail => simp [pushNext.fail, h₁, h₂]
  | char => simp [pushNext.char rfl, h₁, h₂]
  | sparse => simp [pushNext.sparse rfl, h₁, h₂]

theorem εClosure.refines (result result')
  (h : εClosure (BufferStrategy bufferSize) nfa wf it matched next stack = result)
  (h' : εClosure HistoryStrategy nfa wf it matched' next' stack' = result')
  (refMatched : refineUpdateOpt matched' matched)
  (refState : next'.refines next)
  (refStack : stack'.refines stack) :
  refineUpdateOpt result'.1 result.1 ∧ result'.2.refines result.2 := by
  induction matched', next', stack' using εClosure.induct' HistoryStrategy nfa wf it generalizing matched next stack result result' with
  | base matched' next' =>
    simp at refStack
    subst stack
    simp [εClosure.base] at h' h
    simp [←h', ←h, refMatched, refState]
  | visited matched' next' update state' stack' mem ih =>
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure.visited (σ := HistoryStrategy) mem] at h'
      rw [εClosure.visited (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem)] at h
      exact ih result result' h h' refMatched refState rest
  | not_visited matched' next' update state' stack' mem node =>
    rename_i matched'' states'' updates'' ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure.not_visited (σ := HistoryStrategy) mem] at h'
      rw [εClosure.not_visited (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem)] at h
      refine ih result result' h h' ?_ ?_ ?_
      . simp [matched'', node, h₂]
        if eq : nfa[state.val] = .done then
          simp [eq]
          exact refMatched.orElse h₁
        else
          simpa [eq] using refMatched
      . simp [SearchState.refines, states'', updates'', node, h₂, refState.1]
        if write : writeUpdate nfa[state.val] then
          simp [write]
          exact refineUpdates.set_set refState.2 h₁
        else
          simpa [write] using refState.2
      . simp [node, h₂]
        exact pushNext.refines wf h₁ rest

theorem stepChar.refines {currentUpdates currentUpdates' state} (result result')
  (h : stepChar (BufferStrategy bufferSize) nfa wf it currentUpdates next state = result)
  (h' : stepChar HistoryStrategy nfa wf it currentUpdates' next' state = result')
  (refUpdates : refineUpdates currentUpdates' currentUpdates)
  (refState : next'.refines next) :
  refineUpdateOpt result'.1 result.1 ∧ result'.2.refines result.2 := by
  simp [stepChar] at h h'
  split at h'
  next state' hn =>
    simp [hn] at h
    exact εClosure.refines result result' h h' (by simp [refineUpdateOpt]) refState (.cons (refUpdates state) rfl .nil)
  next hn =>
    simp [hn] at h
    simpa [←h', ←h, refineUpdateOpt] using refState

theorem eachStepChar.go.refines {current current' i hle hle'} (result result')
  (h : eachStepChar.go (BufferStrategy bufferSize) nfa wf it current i hle next = result)
  (h' : eachStepChar.go HistoryStrategy nfa wf it current' i hle' next' = result')
  (refCurrent : current'.refines current)
  (refNext : next'.refines next) :
  refineUpdateOpt result'.1 result.1 ∧ result'.2.refines result.2 := by
  induction i, hle', next' using eachStepChar.go.induct' HistoryStrategy nfa wf it generalizing current next result result' with
  | base next' =>
    simp at h'
    simp [refCurrent.1] at h
    simp [←h', ←h, refineUpdateOpt, refNext]
  | done i hlt' next' hn =>
    have hlt : i < current.states.count := refCurrent.1 ▸ hlt'
    have eq : current.states[i] = current'.states[i] := by
      simp [refCurrent.1]
    simp [hlt', hn] at h'
    simp [hlt, eq ▸ hn] at h
    simp [←h', ←h, refineUpdateOpt, refNext]
  | found i hlt' next' hn matched' next'' hstep' isSome' =>
    have hlt : i < current.states.count := refCurrent.1 ▸ hlt'
    have eq : current.states[i] = current'.states[i] := by
      simp [refCurrent.1]
    generalize hstep : stepChar (BufferStrategy bufferSize) nfa wf it current.updates next current.states[i] = stepped
    have refStepChar := stepChar.refines stepped (matched', next'') hstep (eq ▸ hstep') refCurrent.2 refNext
    simp at refStepChar
    have isSome : stepped.1.isSome := by
      simp [refineUpdateOpt.isSome_iff refStepChar.1] at isSome'
      exact isSome'
    rw [eachStepChar.go_found hlt' hn hstep' isSome'] at h'
    rw [eachStepChar.go_found hlt (eq ▸ hn) hstep isSome] at h
    simp [←h', ←h, refStepChar]
  | not_found i hlt' next' hn matched' next'' hstep' isSome' ih =>
    have hlt : i < current.states.count := refCurrent.1 ▸ hlt'
    have eq : current.states[i] = current'.states[i] := by
      simp [refCurrent.1]
    generalize hstep : stepChar (BufferStrategy bufferSize) nfa wf it current.updates next current.states[i] = stepped
    have refStepChar := stepChar.refines stepped (matched', next'') hstep (eq ▸ hstep') refCurrent.2 refNext
    simp at refStepChar
    have isSome : ¬stepped.1.isSome := by
      rw [refineUpdateOpt.isSome_iff refStepChar.1] at isSome'
      exact isSome'
    rw [eachStepChar.go_not_found hlt' hn hstep' isSome'] at h'
    rw [eachStepChar.go_not_found hlt (eq ▸ hn) hstep isSome] at h
    exact ih result result' h h' refCurrent refStepChar.2

theorem eachStepChar.refines {current current'} (result result')
  (h : eachStepChar (BufferStrategy bufferSize) nfa wf it current next = result)
  (h' : eachStepChar HistoryStrategy nfa wf it current' next' = result')
  (refCurrent : current'.refines current)
  (refNext : next'.refines next) :
  refineUpdateOpt result'.1 result.1 ∧ result'.2.refines result.2 :=
  eachStepChar.go.refines result result' h h' refCurrent refNext

theorem captureNext.go.refines {current current' result result'}
  (h : captureNext.go (BufferStrategy bufferSize) nfa wf it matched current next = result)
  (h' : captureNext.go HistoryStrategy nfa wf it matched' current' next' = result')
  (refMatched : refineUpdateOpt matched' matched)
  (refCurrent : current'.refines current)
  (refNext : next'.refines next) :
  refineUpdateOpt result' result := by
  induction it, matched', current', next' using captureNext.go.induct' HistoryStrategy nfa wf generalizing matched current next result result' with
  | not_found it matched' current' next' atEnd =>
    rw [captureNext.go_not_found atEnd] at h'
    rw [captureNext.go_not_found atEnd] at h
    simp [←h', ←h, refMatched]
  | found it matched' current' next' atEnd isEmpty' isSome' =>
    have isEmpty : current.states.isEmpty := refCurrent.1 ▸ isEmpty'
    have isSome : matched.isSome := by
      rw [refineUpdateOpt.isSome_iff refMatched] at isSome'
      exact isSome'
    rw [captureNext.go_found atEnd isEmpty' isSome'] at h'
    rw [captureNext.go_found atEnd isEmpty isSome] at h
    simp [←h', ←h, refMatched]
  | ind_not_found it matched' current' next' stepped' expanded' atEnd isNone₁' =>
    rename_i isNone₂' ih
    let stepped := eachStepChar (BufferStrategy bufferSize) nfa wf it current next
    let expanded := εClosure (BufferStrategy bufferSize) nfa wf it.next .none stepped.2 [(Buffer.empty, ⟨nfa.start, wf.start_lt⟩)]

    have refStepped := eachStepChar.refines stepped stepped' rfl rfl refCurrent refNext
    have refExpanded := εClosure.refines expanded expanded' rfl rfl (by simp [refineUpdateOpt]) refStepped.2 (.cons rfl rfl .nil)
    have isNone₁ : matched = .none := (refineUpdateOpt.none_iff refMatched).mp (by simp [isNone₁'])
    have isNone₂ : stepped.1 = .none := (refineUpdateOpt.none_iff refStepped.1).mp (by simp [isNone₂'])

    rw [captureNext.go_ind_not_found stepped' expanded' rfl rfl atEnd isNone₁' isNone₂'] at h'
    rw [captureNext.go_ind_not_found stepped expanded rfl rfl atEnd isNone₁ isNone₂] at h
    exact ih h h' refExpanded.1 refExpanded.2 (by simp [SearchState.refines, refCurrent.1, refCurrent.2])
  | ind_found it matched' current' next' stepped' atEnd hemp' isSome' =>
    rename_i ih
    let stepped : (Option (Buffer bufferSize)) × SearchState (BufferStrategy bufferSize) nfa :=
      eachStepChar (BufferStrategy bufferSize) nfa wf it current next

    have refStepped := eachStepChar.refines stepped stepped' rfl rfl refCurrent refNext
    have refMatched' : refineUpdateOpt (stepped'.1 <|> matched') (stepped.1 <|> matched) :=
      refineUpdateOpt.orElse refStepped.1 refMatched
    have hemp (h : matched.isSome) : ¬current.states.isEmpty :=
      refCurrent.1 ▸ hemp' ((refineUpdateOpt.isSome_iff refMatched).mpr h)
    have isSome : matched.isSome ∨ stepped.1.isSome := by
      rw [←refineUpdateOpt.isSome_iff refMatched, ←refineUpdateOpt.isSome_iff refStepped.1]
      exact isSome'

    rw [captureNext.go_ind_found stepped' rfl atEnd hemp' isSome'] at h'
    rw [captureNext.go_ind_found stepped rfl atEnd hemp isSome] at h
    exact ih h h' refMatched' refStepped.2 (by simp [SearchState.refines, refCurrent.1, refCurrent.2])

theorem captureNext.refines :
  refineUpdateOpt (captureNext HistoryStrategy nfa wf it) (captureNext (BufferStrategy bufferSize) nfa wf it) := by
  unfold captureNext
  simp
  generalize hexpand' : εClosure HistoryStrategy nfa wf it .none ⟨.empty, Vector.replicate nfa.nodes.size HistoryStrategy.empty⟩ [(HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩)] = expanded'
  generalize hexpand : εClosure (BufferStrategy bufferSize) nfa wf it .none ⟨.empty, Vector.replicate nfa.nodes.size (BufferStrategy bufferSize).empty⟩ [((BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩)] = expanded

  have ⟨refMatched, refState⟩ := εClosure.refines expanded expanded' hexpand hexpand'
    (by simp [refineUpdateOpt]) (by simp [SearchState.refines, refineUpdates]) (.cons rfl rfl .nil)
  exact captureNext.go.refines rfl rfl refMatched refState (by simp [SearchState.refines, refineUpdates])

end Regex.VM
