import Regex.NFA.VM.Basic
import RegexCorrectness.NFA.Transition
import RegexCorrectness.NFA.Correctness

theorem Array.isEmpty_iff {α} {a : Array α} : a.isEmpty ↔ a = #[] := by
  simp [Array.isEmpty]
  apply Iff.intro
  . exact eq_empty_of_size_eq_zero
  . intro h
    simp [h]

theorem Array.mem_back' {a : Array α} (hemp : ¬ a.isEmpty) : a.back' hemp ∈ a := by
  simp [back', Array.mem_def, Array.getElem_eq_data_get]
  apply List.get_mem

theorem Array.mem_push (a : Array α) (x y : α) :
  y ∈ a.push x ↔ y ∈ a ∨ y = x := by
  unfold Array.push
  simp [Array.mem_def]

@[simp]
theorem Array.mem_of_push (a : Array α) (x : α) :
  x ∈ a.push x := by
  simp [Array.mem_def]

theorem Array.push_pop_eq (a : Array α) (hemp : ¬ a.isEmpty) :
  a.pop.push (a.back' hemp) = a := by
  simp at hemp
  have : 0 < a.size := Nat.pos_of_ne_zero hemp
  apply Array.ext
  . simp [Nat.sub_add_cancel this]
  . simp [Nat.sub_add_cancel this]
    intro i h _
    rw [Array.get_push]
    split
    case inl h' => rw [Array.getElem_pop]
    case inr h' =>
      simp at h'
      have : i + 1 - 1 ≤ a.size - 1 := Nat.sub_le_sub_right h _
      simp at this
      have : i = a.size - 1 := Nat.le_antisymm this h'
      simp [back', this]

theorem Array.mem_pop (a : Array α) (x : α) (hemp : ¬ a.isEmpty)
  (mem : x ∈ a) (neq : x ≠ a.back' hemp) : x ∈ a.pop := by
  rw [←Array.push_pop_eq a hemp] at mem
  cases (Array.mem_push _ _ _).mp mem with
  | inl mem => exact mem
  | inr eq => exact absurd eq neq

theorem Array.mem_pop_or_eq_of_mem (a : Array α) (x : α) (hemp : ¬ a.isEmpty)
  (mem : x ∈ a) : x ∈ a.pop ∨ x = a.back' hemp := by
  rw [←Array.push_pop_eq a hemp] at mem
  exact (Array.mem_push _ _ _).mp mem

theorem Array.mem_of_mem_pop (a : Array α) (x : α) (mem : x ∈ a.pop) :
  x ∈ a := by
  cases decEq a.isEmpty true with
  | isTrue hemp =>
    have := (Array.isEmpty_iff).mp hemp
    subst this
    simp at mem
  | isFalse hemp =>
    rw [←Array.push_pop_eq a hemp]
    apply (Array.mem_push _ _ _).mpr
    exact Or.inl mem

namespace NFA.VM

theorem mem_εStep_iff_εClosure_sub {nfa : NFA} {S : Set Nat} :
  (∀ i ∈ S, (_ : i < nfa.nodes.size) → ∀ j ∈ nfa[i].εStep, j ∈ S) ↔
  ∀ i ∈ S, nfa.εClosure i ⊆ S := by
  apply Iff.intro
  . intro assm i mem
    intro k cls
    induction cls with
    | base => exact mem
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [εStep, lt] at step
        exact ih (assm i mem lt j step)
      | isFalse nlt => simp [εStep, nlt] at step
  . intro assm i mem _ j step
    apply Set.mem_of_mem_of_subset _ (assm i mem)
    exact εClosure.step (εStep_of_εStep step) .base

def εClosureTR_spec.inv (nfa : NFA) (i : Fin nfa.nodes.size)
  (visited : NodeSet nfa.nodes.size) (stack : Array (Fin nfa.nodes.size)) : Prop :=
  (visited.get i ∨ i ∈ stack) ∧
  (∀ i j, visited.get i → j.val ∈ nfa[i].εStep → visited.get j ∨ j ∈ stack) ∧
  (∀ j, (visited.get j ∨ j ∈ stack) → j.val ∈ nfa.εClosure i)

theorem εClosureTR_spec.case_visited (inv₀ : inv nfa i visited stack)
  (hemp : ¬ stack.isEmpty) (hvis : NodeSet.get visited (Array.back' stack hemp)) :
  inv nfa i visited stack.pop := by
  simp [inv] at *
  set n := Array.back' stack hemp
  obtain ⟨h₁, h₂, h₃⟩ := inv₀
  refine ⟨?_, ?_, ?_⟩
  . cases h₁ with
    | inl vis => exact .inl vis
    | inr stk =>
      cases decEq i n with
      | isTrue eq => exact .inl (eq ▸ hvis)
      | isFalse ne => exact .inr (Array.mem_pop _ _ _ stk ne)
  . intro i j mem step
    cases h₂ i j mem step with
    | inl vis => exact .inl vis
    | inr stk =>
      -- TODO: Looks like a duplication
      cases decEq j n with
      | isTrue eq => exact .inl (eq ▸ hvis)
      | isFalse ne => exact .inr (Array.mem_pop _ _ _ stk ne)
  . intro j h
    apply h₃
    cases h with
    | inl vis => exact .inl vis
    | inr stk => exact .inr (Array.mem_of_mem_pop _ _ stk)

theorem εClosureTR_spec.case_epsilon (inv₀ : inv nfa i visited stack)
  (hemp : ¬ stack.isEmpty) (hvis : ¬ NodeSet.get visited (Array.back' stack hemp))
  (hn : nfa.nodes[(Array.back' stack hemp).val] = NFA.Node.epsilon next) :
  inv nfa i (visited.set (Array.back' stack hemp)) (stack.pop.push ⟨next, isLt⟩) := by
  simp [inv] at *
  set n := Array.back' stack hemp
  obtain ⟨h₁, h₂, h₃⟩ := inv₀
  refine ⟨?_, ?_, ?_⟩
  . cases h₁ with
    | inl vis => simp [NodeSet.get_set, vis]
    | inr stk =>
      cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
      | inl stk => exact Or.inr ((Array.mem_push _ _ _).mpr (.inl stk))
      | inr eq => simp [eq]
  . intro i j mem step
    rw [NodeSet.get_set] at mem
    split at mem
    case inl eq =>
      simp [←eq, NFA.Node.εStep, get_eq_nodes_get, hn] at step
      simp [←step]
    case inr ne =>
      cases h₂ i j mem step with
      | inl vis => simp [NodeSet.get_set, vis]
      | inr stk =>
          cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
          | inl stk => exact Or.inr ((Array.mem_push _ _ _).mpr (.inl stk))
          | inr eq => simp [eq]
  . intro j mem
    cases mem with
    | inl vis =>
      rw [NodeSet.get_set] at vis
      split at vis
      case inl eq =>
        rw [←eq]
        exact h₃ n (.inr (Array.mem_back' hemp))
      case inr ne => exact h₃ j (.inl vis)
    | inr stk =>
      cases (Array.mem_push _ _ _).mp stk with
      | inl stk => exact h₃ j (.inr (Array.mem_of_mem_pop _ _ stk))
      | inr eq =>
        simp [eq]
        have cls : n.val ∈ nfa.εClosure i := h₃ n (.inr (Array.mem_back' hemp))
        have step : next ∈ nfa.εStep n := by
          simp [εStep, NFA.Node.εStep, get_eq_nodes_get, hn]
        exact εClosure_snoc cls step

theorem εClosureTR_spec.case_split (inv₀ : inv nfa i visited stack)
  (hemp : ¬ stack.isEmpty) (hvis : ¬ NodeSet.get visited (Array.back' stack hemp))
  (hn : nfa.nodes[(Array.back' stack hemp).val] = NFA.Node.split next₁ next₂) :
  inv nfa i (visited.set (Array.back' stack hemp)) ((stack.pop.push ⟨next₁, isLt₁⟩).push ⟨next₂, isLt₂⟩) := by
  simp [inv] at *
  set n := Array.back' stack hemp
  obtain ⟨h₁, h₂, h₃⟩ := inv₀
  refine ⟨?_, ?_, ?_⟩
  . cases h₁ with
    | inl vis => simp [NodeSet.get_set, vis]
    | inr stk =>
      cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
      | inl stk =>
        exact Or.inr ((Array.mem_push _ _ _).mpr (.inl ((Array.mem_push _ _ _).mpr (.inl stk))))
      | inr eq => simp [eq]
  . intro i j mem step
    rw [NodeSet.get_set] at mem
    split at mem
    case inl eq =>
      simp [NFA.Node.εStep, get_eq_nodes_get, ←eq, hn] at step
      cases step with
      | inl eq₁ => simp [←eq₁, Array.mem_push]
      | inr eq₂ => simp [←eq₂]
    case inr ne =>
      cases h₂ i j mem step with
      | inl vis => simp [NodeSet.get_set, vis]
      | inr stk =>
        cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
        | inl stk =>
          exact Or.inr ((Array.mem_push _ _ _).mpr (.inl ((Array.mem_push _ _ _).mpr (.inl stk))))
        | inr eq => simp [eq]
  . intro j mem
    have ncls : n.val ∈ nfa.εClosure i := h₃ n (.inr (Array.mem_back' hemp))
    cases mem with
    | inl vis =>
      rw [NodeSet.get_set] at vis
      split at vis
      case inl eq => exact eq ▸ ncls
      case inr ne => exact h₃ j (.inl vis)
    | inr stk =>
      cases (Array.mem_push _ _ _).mp stk with
      | inl stk =>
        cases (Array.mem_push _ _ _).mp stk with
        | inl stk => exact h₃ j (.inr (Array.mem_of_mem_pop _ _ stk))
        | inr eq =>
          simp [eq]
          have step : next₁ ∈ nfa.εStep n := by
            simp [εStep, NFA.Node.εStep, get_eq_nodes_get, hn]
          exact εClosure_snoc ncls step
      | inr eq =>
        simp [eq]
        have step : next₂ ∈ nfa.εStep n := by
          simp [εStep, NFA.Node.εStep, get_eq_nodes_get, hn]
        exact εClosure_snoc ncls step

theorem εClosureTR_spec.case_else (inv₀ : inv nfa i visited stack)
  (hemp : ¬ stack.isEmpty) (hvis : ¬ NodeSet.get visited (Array.back' stack hemp))
  (hn₁ : ∀ (next : Nat), ¬ nfa.nodes[(Array.back' stack hemp).val] = NFA.Node.epsilon next)
  (hn₂ : ∀ (next₁ next₂ : Nat), ¬ nfa.nodes[(Array.back' stack hemp).val] = NFA.Node.split next₁ next₂) :
  inv nfa i (visited.set (Array.back' stack hemp)) stack.pop := by
  simp [inv] at *
  set n := Array.back' stack hemp
  obtain ⟨h₁, h₂, h₃⟩ := inv₀
  refine ⟨?_, ?_, ?_⟩
  . cases h₁ with
    | inl vis => simp [NodeSet.get_set, vis]
    | inr stk =>
      cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
      | inl stk => exact Or.inr stk
      | inr eq => simp [eq]
  . intro i j mem step
    rw [NodeSet.get_set] at mem
    split at mem
    case inl eq =>
      exfalso
      simp [eq.symm, NFA.Node.εStep] at step
      split at step
      next next hn => exact absurd hn (hn₁ next)
      next next₁ next₂ hn => exact absurd hn (hn₂ next₁ next₂)
      next hn => contradiction
    case inr ne =>
      cases h₂ i j mem step with
      | inl vis => simp [NodeSet.get_set, vis]
      | inr stk =>
        cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
        | inl stk => exact Or.inr stk
        | inr eq => simp [eq]
  . intro j mem
    cases mem with
    | inl vis =>
      cases decEq j n with
      | isTrue eq =>
        rw [eq]
        have : n ∈ stack := Array.mem_back' hemp
        exact h₃ n (.inr this)
      | isFalse neq =>
        rw [NodeSet.get_set_ne] at vis
        . exact h₃ j (.inl vis)
        . intro h
          exact neq (Fin.eq_of_val_eq h).symm
    | inr stk =>
      have : j ∈ stack := Array.mem_of_mem_pop _ _ stk
      exact h₃ j (.inr this)

-- The case analysis takes a bit of time, so we split each branch as lemmas
theorem εClosureTR_spec.go (nfa : NFA) (i : Fin nfa.nodes.size) {visited stack}
  (inv₀ : inv nfa i visited stack) :
  inv nfa i (εClosureTR nfa visited stack) #[] := by
  unfold εClosureTR
  split
  case inl hemp => exact (Array.isEmpty_iff.mp hemp) ▸ inv₀
  case inr hemp =>
    have : stack.pop.size < stack.size := Array.lt_size_of_pop_of_not_empty _ hemp
    simp
    split
    case inl hvis => exact go nfa i (case_visited inv₀ hemp hvis)
    case inr hvis =>
      have : (visited.set (Array.back' stack hemp)).count_unset < visited.count_unset :=
        visited.lt_count_unset _ hvis
      split
      next hn => exact go nfa i (case_epsilon inv₀ hemp hvis hn)
      next hn => exact go nfa i (case_split inv₀ hemp hvis hn)
      next hn₁ hn₂ => exact go nfa i (case_else inv₀ hemp hvis hn₁ hn₂)
termination_by (visited.count_unset, stack.size)

theorem εClosureTR_spec {nfa : NFA} {i : Fin nfa.nodes.size} :
  ∀ j, (εClosureTR nfa .empty #[i]).get j ↔ j.val ∈ nfa.εClosure i := by
  have inv₀ : εClosureTR_spec.inv nfa i .empty #[i] := by
    simp [εClosureTR_spec.inv]
    exact .base
  have ⟨h₁, h₂, h₃⟩ := εClosureTR_spec.go nfa i inv₀
  simp at h₁ h₂ h₃
  intro j
  apply Iff.intro
  . exact h₃ j
  . intro h
    let S := { j | ∃ lt : j < nfa.nodes.size, (εClosureTR nfa .empty #[i]).get ⟨j, lt⟩ }
    have mem : i.val ∈ S := by
      simp [h₁]
    have : ∀ j ∈ S, (_ : j < nfa.nodes.size) → ∀ k ∈ nfa[j].εStep, k ∈ S := by
      intro j mem _ k step
      simp at mem
      obtain ⟨_, get⟩ := mem
      simp
      have klt : k < nfa.nodes.size := lt_of_εStep step
      have := h₂ _ ⟨k, klt⟩ get
      refine ⟨klt, this ?_⟩
      simp [step]

    have := mem_εStep_iff_εClosure_sub.mp this i mem
    have := Set.mem_of_mem_of_subset h this
    simp at this
    exact this

def charStepTR_spec.inv (nfa : NFA) (c : Char) (init : NodeSet nfa.nodes.size)
  (accum : NodeSet nfa.nodes.size) (i : Nat) : Prop :=
  ∀ k, accum.get k ↔ k.val ∈ nfa.stepSet { j | j < i ∧ ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } c

theorem charStepTR_spec.lem (nfa : NFA) (init : NodeSet nfa.nodes.size)
  (i : Nat) (hlt : i < nfa.nodes.size) :
  { j | j < i + 1 ∧ ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } =
  if init.get ⟨i, hlt⟩ then
    { j | j < i ∧ ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } ∪ {i}
  else
    { j | j < i ∧ ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } := by
  split
  case inl hset =>
    apply Set.eq_of_subset_of_subset
    . intro j
      simp
      intro lt₁ lt₂ hset'
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt₁) with
      | inl lt₃ => exact .inr ⟨lt₃, lt₂, hset'⟩
      | inr eq => exact .inl eq
    . intro j
      simp
      intro h
      match h with
      | .inl eq => simp [eq, hlt, hset]
      | .inr ⟨lt₁, lt₂, hset'⟩ => exact ⟨Nat.lt_trans lt₁ (Nat.lt_succ_self _), lt₂, hset'⟩
  case inr hset =>
    apply Set.eq_of_subset_of_subset
    . intro j
      simp
      intro lt₁ lt₂ hset'
      cases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ lt₁) with
      | inl lt₃ => exact ⟨lt₃, lt₂, hset'⟩
      | inr eq => simp [eq, hset] at hset'
    . intro j
      simp
      intro lt₁ lt₂ hset'
      exact ⟨Nat.lt_trans lt₁ (Nat.lt_succ_self _), lt₂, hset'⟩

theorem charStepTR_spec.go (nfa : NFA) (c : Char) (init : NodeSet nfa.nodes.size)
  (accum : NodeSet nfa.nodes.size) (i : Nat) (hle : i ≤ nfa.nodes.size)
  (inv₀ : inv nfa c init accum i) :
  ∀ k, ((charStepTR.go nfa c init accum i hle)).get k ↔
  k.val ∈ nfa.stepSet { j | ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } c := by
  unfold charStepTR.go
  split
  case inl eq =>
    have : { j | j < i ∧ ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ }
      = { j | ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } := by
      apply Set.eq_of_subset_of_subset
      . intro j h
        simp at *
        obtain ⟨_, ⟨lt, mem⟩⟩ := h
        exact ⟨lt, mem⟩
      . intro j h
        simp at *
        exact ⟨eq ▸ h.1, h⟩
    rw [inv, this] at inv₀
    exact inv₀
  case inr ne =>
    simp
    have hlt : i < nfa.nodes.size := Nat.lt_of_le_of_ne hle ne
    apply go nfa c init _ (i + 1) hlt
    split
    case inl hset =>
      simp [inv, lem nfa init i hlt, hset, stepSet_insert_distrib]
      split
      next next hn =>
        split
        case inl eqc =>
          intro k
          apply Iff.intro
          . intro hset
            simp [NodeSet.merge_get] at hset
            cases hset with
            | inl hset => exact .inl ((inv₀ k).mp hset)
            | inr hset =>
              apply Or.inr
              simp [εClosureTR_spec k] at hset
              simp [stepSet, εClosureSet]
              refine ⟨next, ?_, hset⟩
              simp [charStep, get_eq_nodes_get, NFA.Node.charStep, hn, eqc, hlt]
          . intro hset
            simp [NodeSet.merge_get]
            cases hset with
            | inl hset => exact .inl ((inv₀ k).mpr hset)
            | inr hset =>
              apply Or.inr
              simp [εClosureTR_spec k]
              simp [stepSet, εClosureSet, charStep, get_eq_nodes_get, NFA.Node.charStep, hn, eqc, hlt] at hset
              exact hset
        case inr nec =>
          have : nfa.stepSet {i} c = ∅ := by
            simp [stepSet, charStep, NFA.Node.charStep, get_eq_nodes_get, hn, nec]
          simp [this]
          exact inv₀
      next hn =>
        split
        case inr x =>
          simp [inv] at inv₀
          intro k
          refine ⟨fun x => Or.inl ((inv₀ k).mp x), ?y⟩
          intro r
          let f := (inv₀ k).mpr
          cases r with
          | inl hset => exact f hset
          | inr hset =>
            simp [stepSet, εClosureSet, NFA.εClosure, charStep, hlt, hn,  GetElem.getElem] at hset
            simp [NFA.get, hn, Node.charStep, x, hn] at hset
        case inl x =>
          simp [inv] at inv₀
          intro k
          apply Iff.intro
          simp [NodeSet.merge_get]
          intro j
          cases j with
          | inl hset => exact .inl ((inv₀ k).mp hset)
          | inr hset =>
            apply Or.inr
            simp [εClosureTR_spec k] at hset
            simp [stepSet, εClosureSet, charStep, GetElem.getElem]
            simp [NFA.get, Node.charStep, x, hn, hlt]
            exact hset
          intro j
          cases j with
          | inl hset =>
            simp [NodeSet.merge_get]
            exact .inl ((inv₀ k).mpr hset)
          | inr hset =>
            simp [NodeSet.merge_get]
            apply Or.inr
            simp [εClosureTR_spec k]
            simp [stepSet, εClosureSet, charStep, GetElem.getElem, hlt, charStep] at hset
            simp [NFA.get, Node.charStep, x, hn, hlt] at hset
            exact hset
      next hn =>
        have : nfa.stepSet {i} c = ∅ := by
          simp [stepSet, charStep, NFA.Node.charStep, get_eq_nodes_get, hn]
        simp [this]
        exact inv₀
    case inr hset =>
      simp [inv, lem nfa init i hlt, hset]
      exact inv₀
termination_by nfa.nodes.size - i

theorem charStepTR_spec (nfa : NFA) (c : Char) (init : NodeSet nfa.nodes.size) :
  ∀ k, (charStepTR nfa c init).get k ↔
  k.val ∈ nfa.stepSet { j | ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } c := by
  have inv₀ : charStepTR_spec.inv nfa c init .empty 0 := by
    simp [charStepTR_spec.inv, Nat.not_lt_zero]
  exact charStepTR_spec.go nfa c init .empty 0 (Nat.zero_le _) inv₀

theorem charStepTR_empty {nfa : NFA} {c : Char} :
  charStepTR nfa c .empty = .empty := by
  ext i
  simp
  by_contra h
  simp [charStepTR_spec] at h

theorem match.go_iff_mem_foldl_stepSet {nfa : NFA} {ns : NodeSet nfa.nodes.size}
  {it : String.Iterator} {cs cs' : List Char} (v : it.ValidFor cs cs') :
  ∀ j, (match.go nfa it ns).get j ↔
  j.val ∈ List.foldl nfa.stepSet { i | ∃ h : i < nfa.nodes.size, ns.get ⟨i, h⟩ } cs' := by
  induction cs' generalizing it cs ns with
  | nil =>
    unfold match.go
    have : it.atEnd := v.atEnd.mpr rfl
    simp [this]
  | cons c cs' ih =>
    unfold match.go
    have : ¬ it.atEnd := v.atEnd.not.mpr (by simp)
    simp [this]
    if h : ns.count_set = 0 then
      simp [h]
      have : ns = .empty := NodeSet.eq_empty_of_count_set_zero h
      simp [this, foldl_stepSet_empty]
    else
      simp [h, v.curr]
      intro j
      rw [ih v.next j]
      congr!
      simp [charStepTR_spec]
      apply Set.eq_of_subset_of_subset
      . intro i
        simp
      . intro i mem
        simp
        exact ⟨lt_of_mem_stepSet mem, mem⟩

theorem evalFrom_iff_match {nfa : NFA} {s : String} :
  nfa.match s ↔ 0 ∈ nfa.evalFrom {nfa.start.val} s.data := by
  unfold NFA.match NFA.evalFrom
  simp [match.go_iff_mem_foldl_stepSet s.validFor_mkIterator]
  simp [εClosureTR_spec, εClosureSet]
  congr!
  apply Set.eq_of_subset_of_subset
  . intro i
    simp
  . intro i mem
    simp
    exact ⟨lt_of_εClosure_right nfa.start.isLt mem, mem⟩

theorem match_iff_regex_matches (eq : NFA.compile r = nfa) :
  nfa.match s ↔ r.matches s := by
  rw [evalFrom_iff_match]
  exact ⟨matches_of_compile_evalFrom eq, evalFrom_of_compile_matches eq⟩

end NFA.VM
