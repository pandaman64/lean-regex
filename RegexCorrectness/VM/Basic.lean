-- Correctness of the graph traversal implementation
import RegexCorrectness.Data.String
import RegexCorrectness.VM.Auxiliary

open Regex.Data (SparseSet Vec)
open Regex.NFA

namespace Regex.VM

structure captureNext.go.Inv (nfa : NFA) (it : String.Iterator) (haystack : String)
  (current : SparseSet nfa.nodes.size) (lastMatch : Option (Array (Option String.Pos))) where
  currentClosure : ∀ i j : Fin nfa.nodes.size, i ∈ current → j.val ∈ nfa.εStep i → j ∈ current
  -- For all states in `current`, there is a path from `nfa.start` to it, the match starting at `l`.
  -- The matching substring corresponds to `m`, and `r` denotes the remaining input.
  currentPath : ∀ i, i ∈ current → ∃ (s : Substring) (l m r : List Char),
    s.ValidFor l m r ∧ it.ValidFor (m.reverse ++ l.reverse) r ∧ nfa.reaches i m
  acceptOfLastMatch : lastMatch.isSome → ∃ (s : Substring) (l m r : List Char),
    s.ValidFor l m r ∧ haystack = ⟨l ++ m ++ r⟩ ∧ ∃ i, nfa.reaches i m ∧ nfa[i] = .done

theorem captureNext_spec.go
  (h : captureNext.go nfa wf saveSize it current next saveSlots lastMatch = matched)
  (inv : captureNext.go.Inv nfa it haystack current lastMatch)
  (v : it.Valid)
  (eqs : haystack = it.toString)
  (hemp : next.isEmpty) :
  matched.isSome → ∃ (s : Substring) (l m r : List Char),
    s.ValidFor l m r ∧ haystack = ⟨l ++ m ++ r⟩ ∧ ∃ i, nfa.reaches i m ∧ nfa[i] = .done := by
  unfold captureNext.go at h
  split at h
  next =>
    subst h
    exact eqs ▸ inv.acceptOfLastMatch
  next atEnd =>
    split at h
    next h' =>
      subst h
      exact eqs ▸ inv.acceptOfLastMatch
    next =>
      if hm : lastMatch.isNone then
        generalize he : exploreεClosure nfa wf it.pos current (captureNext.initSave saveSize) none saveSlots ⟨nfa.start, wf.start_lt⟩ #[] = explored at h
        let (_, current', saveSlots') := explored
        simp [hm] at h
        have mem_current'_iff := exploreεClosure_spec.mem_next_iff he inv.currentClosure

        generalize hs : eachStepChar nfa wf it.curr it.next.i current' next saveSlots' = stepped at h
        let (matched', next', saveSlots'') := stepped
        simp at h

        have currentPath'  (k : Fin nfa.nodes.size) (hk : k ∈ next') :
          ∃ (s : Substring) (l m r : List Char), s.ValidFor l m r ∧ it.next.ValidFor (m.reverse ++ l.reverse) r ∧ nfa.reaches k m := by
          have ⟨_, mem_next_iff⟩ := eachStepChar_spec.mem_next_iff hs hemp
          have ⟨i, isLt, _, ⟨j, step, cls⟩⟩ := (mem_next_iff k).mp hk
          cases (mem_current'_iff current'[i]).mp (SparseSet.mem_get isLt) with
          | inl mem_current =>
            -- Previous search continues
            have ⟨s, l, m, r, sv, iv, prev⟩ := inv.currentPath current'[i] mem_current
            have ⟨r', hr⟩ := iv.exists_cons_of_not_atEnd atEnd
            subst hr
            exact ⟨s.expand, l, m ++ [it.curr], r', sv.expand, by simp [iv.next], prev.snoc step cls⟩
          | inr cls' =>
            -- New search from `it.pos`
            have ⟨l, r, iv⟩ := v.validFor
            have ⟨r', hr⟩ := iv.exists_cons_of_not_atEnd atEnd
            subst hr
            let startPos : String.Pos := ⟨String.utf8Len l⟩
            refine ⟨⟨it.toString, startPos, startPos + it.curr⟩, l.reverse, [it.curr], r', ?_, ?_, ?_⟩
            . apply Substring.ValidFor.of_eq <;> simp [iv.toString, List.reverseAux_eq]
            . apply String.Iterator.ValidFor.of_eq <;> simp [iv.next.toString, iv.next.pos]
            . have prev : nfa.reaches current'[i] [] := .nil cls'
              exact prev.snoc step cls

        have acceptOfLastMatch' (h : (matched' <|> lastMatch).isSome) :
          ∃ (s : Substring) (l m r : List Char), s.ValidFor l m r ∧ haystack = ⟨l ++ m ++ r⟩ ∧ ∃ i, nfa.reaches i m ∧ nfa[i] = .done := by
          cases matched' with
          | none =>
            simp at h
            exact eqs ▸ inv.acceptOfLastMatch h
          | some =>
            have ⟨i, hi, hdone⟩ := (eachStepChar_spec.mem_done_iff hs hemp).mpr rfl
            have ⟨s, l, m, r, sv, iv, reaches⟩ := currentPath' i hi
            have eqs' := iv.toString
            simp [String.Iterator.next, List.reverseAux_eq] at eqs'
            exact ⟨s, l, m, r, sv, by simp [eqs, eqs'], ⟨i, reaches, hdone⟩⟩

        have inv' : captureNext.go.Inv nfa it.next haystack next' (matched' <|> lastMatch) :=
          ⟨eachStepChar_spec.preserve_cls hs hemp, currentPath', acceptOfLastMatch'⟩
        exact captureNext_spec.go h inv' (v.next' atEnd) (by simp [eqs, String.Iterator.next]) (by simp)
      else
        simp [hm] at h

        generalize hs : eachStepChar nfa wf it.curr it.next.i current next saveSlots = stepped at h
        let (matched', next', saveSlots'') := stepped
        simp at h

        have currentPath' (k : Fin nfa.nodes.size) (hk : k ∈ next') :
          ∃ (s : Substring) (l m r : List Char), s.ValidFor l m r ∧ it.next.ValidFor (m.reverse ++ l.reverse) r ∧ nfa.reaches k m := by
          have ⟨_, mem_next_iff⟩ := eachStepChar_spec.mem_next_iff hs hemp
          have ⟨i, isLt, _, ⟨j, step, cls⟩⟩ := (mem_next_iff k).mp hk
          have ⟨s, l, m, r, sv, iv, prev⟩ := inv.currentPath current[i] (SparseSet.mem_get isLt)
          have ⟨r', hr⟩ := iv.exists_cons_of_not_atEnd atEnd
          subst hr
          exact ⟨s.expand, l, m ++ [it.curr], r', sv.expand, by simp [iv.next], prev.snoc step cls⟩

        have acceptOfLastMatch' (h : (matched' <|> lastMatch).isSome) :
          ∃ (s : Substring) (l m r : List Char), s.ValidFor l m r ∧ haystack = ⟨l ++ m ++ r⟩ ∧ ∃ i, nfa.reaches i m ∧ nfa[i] = .done := by
          cases matched' with
          | none =>
            simp at h
            exact eqs ▸ inv.acceptOfLastMatch h
          | some =>
            have ⟨i, hi, hdone⟩ := (eachStepChar_spec.mem_done_iff hs hemp).mpr rfl
            have ⟨s, l, m, r, sv, iv, reaches⟩ := currentPath' i hi
            have eqs' := iv.toString
            simp [String.Iterator.next, List.reverseAux_eq] at eqs'
            exact ⟨s, l, m, r, sv, by simp [eqs, eqs'], ⟨i, reaches, hdone⟩⟩

        have inv' : captureNext.go.Inv nfa it.next haystack next' (matched' <|> lastMatch) :=
          ⟨eachStepChar_spec.preserve_cls hs hemp, currentPath', acceptOfLastMatch'⟩
        exact captureNext_spec.go h inv' (v.next' atEnd) (by simp [eqs, String.Iterator.next]) (by simp)

theorem captureNext_spec
  (h : captureNext nfa wf it saveSize = matched)
  (v : it.Valid)
  (hsome : matched.isSome) :
  ∃ (s : Substring) (l m r : List Char),
    s.ValidFor l m r ∧ it.toString = ⟨l ++ m ++ r⟩ ∧ ∃ i, nfa.reaches i m ∧ nfa[i] = .done := by
  unfold captureNext at h
  generalize _hs : Vec.ofFn (fun _ => captureNext.initSave saveSize) = saveSlots at h
  simp at h
  generalize he : exploreεClosure nfa wf it.i .empty (captureNext.initSave saveSize) .none saveSlots ⟨nfa.start, wf.start_lt⟩ #[] = init at h
  let (matched', init', saveSlots) := init
  simp at h

  have hnotMem (i : Fin nfa.nodes.size) : ¬i ∈ SparseSet.empty := by
    simp only [SparseSet.not_mem_of_isEmpty SparseSet.isEmpty_empty]
    simp

  have inv : captureNext.go.Inv nfa it it.toString init' matched' := by
    refine ⟨exploreεClosure_spec.preserve_cls he (by simp only [hnotMem]; simp), ?_, ?_⟩
    . intro i hi
      have ⟨l, r, v'⟩ := v.validFor
      let pos : String.Pos := ⟨String.utf8Len l⟩
      refine ⟨⟨it.toString, pos, pos⟩, l.reverse, [], r, ?_, by simp [v'], .nil ?_⟩
      . apply Substring.ValidFor.of_eq <;> simp [v'.toString, List.reverseAux_eq]
      . have := (exploreεClosure_spec.mem_next_iff he (by simp only [hnotMem]; simp) i).mp hi
        simp only [hnotMem] at this
        simp at this
        exact this
    . intro hsome
      have ⟨i, hi, hdone⟩ := (exploreεClosure_mem_done_iff he (by simp only [hnotMem]; simp)).mpr hsome
      have cls := (exploreεClosure_spec.mem_next_iff he (by simp only [hnotMem]; simp) i).mp hi
      simp only [hnotMem] at cls
      simp at cls
      have ⟨l, r, v'⟩ := v.validFor
      let pos : String.Pos := ⟨String.utf8Len l⟩
      refine ⟨⟨it.toString, pos, pos⟩, l.reverse, [], r, ?_, by simp [v'.toString, List.reverseAux_eq], ⟨i, .nil cls, hdone⟩⟩
      apply Substring.ValidFor.of_eq <;> simp [v'.toString, List.reverseAux_eq]
  exact captureNext_spec.go h inv v rfl (by simp) hsome

end Regex.VM
