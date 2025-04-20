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

theorem εClosure.refines {result result'}
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
    simp at h' h
    simp [←h', ←h, refMatched, refState]
  | visited matched' next' update state' stack' mem ih =>
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_visited (σ := HistoryStrategy) mem] at h'
      rw [εClosure_visited (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem)] at h
      exact ih h h' refMatched refState rest
  | epsilon matched' next' update state' stack' state mem hn next'' =>
    -- TODO: cannot introduce `ih` directly for some reason
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_epsilon (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_epsilon (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have : next''.refines ⟨next.states.insert state, next.updates⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        exact refState.2
      exact ih h h' refMatched this (.cons h₁ rfl rest)
  | anchor_pos matched' next' update state stack' anchor state' mem hn next'' test =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_anchor_pos (σ := HistoryStrategy) mem hn test] at h'
      rw [εClosure_anchor_pos (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn) test] at h
      have : next''.refines ⟨next.states.insert state, next.updates⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        exact refState.2
      exact ih h h' refMatched this (.cons h₁ rfl rest)
  | anchor_neg matched' next' update state stack' anchor state' mem hn next'' test =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_anchor_neg (σ := HistoryStrategy) mem hn test] at h'
      rw [εClosure_anchor_neg (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn) test] at h
      have : next''.refines ⟨next.states.insert state, next.updates⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        exact refState.2
      exact ih h h' refMatched this rest
  | split matched' next' update state stack' state₁ state₂ mem hn next'' =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_split (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_split (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have : next''.refines ⟨next.states.insert state, next.updates⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        exact refState.2
      exact ih h h' refMatched this (.cons h₁ rfl (.cons h₁ rfl rest))
  | save matched' next' update state stack' offset state' mem hn next'' =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_save (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_save (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have : next''.refines ⟨next.states.insert state, next.updates⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        exact refState.2
      exact ih h h' refMatched this (.cons (by simp [h₁, HistoryStrategy, BufferStrategy]) rfl rest)
  | done matched' next' update state stack' mem hn next'' =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_done (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_done (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have refMatched' : refineUpdateOpt (matched' <|> some update) (matched <|> some buffer) :=
        refineUpdateOpt.orElse refMatched h₁
      have : next''.refines ⟨next.states.insert state, next.updates.set state buffer⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        intro i
        if h : state = i then
          simp [h]
          exact h₁
        else
          have : state.val ≠ i := Fin.val_ne_of_ne h
          simp [this]
          exact refState.2 i
      exact ih h h' refMatched' this rest
  | char matched' next' update state stack' c state' mem hn next'' =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_char (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_char (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have : next''.refines ⟨next.states.insert state, next.updates.set state buffer⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        intro i
        if h : state = i then
          simp [h]
          exact h₁
        else
          have : state.val ≠ i := Fin.val_ne_of_ne h
          simp [this]
          exact refState.2 i
      exact ih h h' refMatched this rest
  | sparse matched' next' update state stack' cs state' mem hn next'' =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_sparse (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_sparse (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have : next''.refines ⟨next.states.insert state, next.updates.set state buffer⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        intro i
        if h : state = i then
          simp [h]
          exact h₁
        else
          have : state.val ≠ i := Fin.val_ne_of_ne h
          simp [this]
          exact refState.2 i
      exact ih h h' refMatched this rest
  | fail matched' next' update state stack' mem hn next'' =>
    rename_i ih
    cases refStack with
    | @cons _ _ tail' buffer state tail h₁ h₂ rest =>
      rw [εClosure_fail (σ := HistoryStrategy) mem hn] at h'
      rw [εClosure_fail (σ := BufferStrategy bufferSize) (refState.1 ▸ h₂ ▸ mem) (h₂ ▸ hn)] at h
      have : next''.refines ⟨next.states.insert state, next.updates⟩ := by
        simp [SearchState.refines, h₂, refState.1, next'']
        exact refState.2
      exact ih h h' refMatched this rest

theorem stepChar.refines {currentUpdates currentUpdates' state result result'}
  (h : stepChar (BufferStrategy bufferSize) nfa wf it currentUpdates next state = result)
  (h' : stepChar HistoryStrategy nfa wf it currentUpdates' next' state = result')
  (refUpdates : refineUpdates currentUpdates' currentUpdates)
  (refState : next'.refines next) :
  refineUpdateOpt result'.1 result.1 ∧ result'.2.refines result.2 := by
  unfold stepChar at h'
  split at h'
  next c state' hn =>
    rw [stepChar_char hn] at h
    split at h'
    next eq =>
      simp [eq] at h h'
      exact εClosure.refines h h' (by simp [refineUpdateOpt]) refState (.cons (refUpdates state) rfl .nil)
    next ne =>
      simp [ne] at h
      simp [←h', ←h, refineUpdateOpt, refState]
  next cs state' hn =>
    rw [stepChar_sparse hn] at h
    split at h'
    next mem =>
      simp [mem] at h h'
      exact εClosure.refines h h' (by simp [refineUpdateOpt]) refState (.cons (refUpdates state) rfl .nil)
    next nmem =>
      simp [nmem] at h
      simp [←h', ←h, refineUpdateOpt, refState]
  next h₁ h₂ =>
    rw [stepChar_not_char_sparse h₁ h₂] at h
    simp [←h', ←h, refineUpdateOpt, refState]

theorem eachStepChar.go.refines {current current' i hle hle' result result'}
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
    have refStepChar := stepChar.refines hstep (eq ▸ hstep') refCurrent.2 refNext
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
    have refStepChar := stepChar.refines hstep (eq ▸ hstep') refCurrent.2 refNext
    simp at refStepChar
    have isSome : ¬stepped.1.isSome := by
      rw [refineUpdateOpt.isSome_iff refStepChar.1] at isSome'
      exact isSome'
    rw [eachStepChar.go_not_found hlt' hn hstep' isSome'] at h'
    rw [eachStepChar.go_not_found hlt (eq ▸ hn) hstep isSome] at h
    exact ih h h' refCurrent refStepChar.2

theorem eachStepChar.refines {current current' result result'}
  (h : eachStepChar (BufferStrategy bufferSize) nfa wf it current next = result)
  (h' : eachStepChar HistoryStrategy nfa wf it current' next' = result')
  (refCurrent : current'.refines current)
  (refNext : next'.refines next) :
  refineUpdateOpt result'.1 result.1 ∧ result'.2.refines result.2 :=
  eachStepChar.go.refines h h' refCurrent refNext

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
  | ind_not_found it matched' current' next' _ current'' matched'' next'' atEnd isNone' h₁ h₂ ih =>
    have isNone : matched.isNone := by
      rw [refineUpdateOpt.isNone_iff refMatched] at isNone'
      exact isNone'
    generalize hexpand : εClosure (BufferStrategy bufferSize) nfa wf it .none current [(Buffer.empty, ⟨nfa.start, wf.start_lt⟩)] = expanded
    generalize hstep : eachStepChar (BufferStrategy bufferSize) nfa wf it expanded.2 next = stepped
    rw [captureNext.go_ind_not_found atEnd isNone' h₁ h₂] at h'
    rw [captureNext.go_ind_not_found atEnd isNone hexpand hstep] at h

    have refExpanded := εClosure.refines hexpand h₁ (by simp [refineUpdateOpt]) refCurrent (.cons rfl rfl .nil)
    simp at refExpanded
    have ⟨refMatched'', refNext''⟩ := eachStepChar.refines hstep h₂ refExpanded.2 refNext
    simp at refMatched'' refNext''
    exact ih h h' refMatched'' refNext'' (by simp [SearchState.refines, refExpanded.2.1, refExpanded.2.2])
  | ind_found it matched' current' next' matched'' next'' atEnd isEmpty' isSome' h'' ih =>
    have isEmpty : ¬current.states.isEmpty := refCurrent.1 ▸ isEmpty'
    have isSome : matched.isSome := by
      rw [refineUpdateOpt.isSome_iff refMatched] at isSome'
      exact isSome'
    generalize hstep : eachStepChar (BufferStrategy bufferSize) nfa wf it current next = stepped
    simp [BufferStrategy] at stepped
    rw [captureNext.go_ind_found atEnd isEmpty' isSome' h''] at h'
    rw [captureNext.go_ind_found atEnd isEmpty isSome hstep] at h

    have := eachStepChar.refines hstep h'' refCurrent refNext
    simp at this
    have ⟨refMatched'', refNext''⟩ := this
    have : refineUpdateOpt (matched'' <|> matched') (stepped.1 <|> matched) :=
      refineUpdateOpt.orElse refMatched'' refMatched
    exact ih h h' this refNext'' (by simp [refCurrent.1, SearchState.refines, refCurrent.2])

theorem captureNext.refines :
  refineUpdateOpt (captureNext HistoryStrategy nfa wf it) (captureNext (BufferStrategy bufferSize) nfa wf it) := by
  unfold captureNext
  simp
  generalize hexpand' : εClosure HistoryStrategy nfa wf it .none ⟨.empty, Vector.mkVector nfa.nodes.size HistoryStrategy.empty⟩ [(HistoryStrategy.empty, ⟨nfa.start, wf.start_lt⟩)] = expanded'
  generalize hexpand : εClosure (BufferStrategy bufferSize) nfa wf it .none ⟨.empty, Vector.mkVector nfa.nodes.size (BufferStrategy bufferSize).empty⟩ [((BufferStrategy bufferSize).empty, ⟨nfa.start, wf.start_lt⟩)] = expanded

  have ⟨refMatched, refState⟩ := εClosure.refines hexpand hexpand'
    (by simp [refineUpdateOpt]) (by simp [SearchState.refines, refineUpdates]) (.cons rfl rfl .nil)
  exact captureNext.go.refines rfl rfl refMatched refState (by simp [SearchState.refines, refineUpdates])

end Regex.VM
