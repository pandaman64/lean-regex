import Regex.NFA.VM.Basic
import RegexCorrectness.NFA.Transition
import RegexCorrectness.NFA.Correctness

theorem Array.isEmpty_iff {α} {a : Array α} : a.isEmpty ↔ a = #[] := by
  have : a.isEmpty ↔ a.data = [] := by
    simp [Array.isEmpty, Array.size]
    match a.data with
    | [] => simp
    | _ :: _ => simp
  rw [this]
  apply Iff.intro
  . intro h
    apply Array.ext'
    simp [h]
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
    simp [Set.subset_def]
    intro k cls
    induction cls with
    | base => exact mem
    | @step i j k step _ ih =>
      cases Nat.decLt i nfa.nodes.size with
      | isTrue lt =>
        simp [getElem?_pos nfa i lt, Option.εStep] at step
        exact ih (assm i mem lt j step)
      | isFalse nlt => simp [getElem?_neg nfa i nlt, Option.εStep] at step
  . intro assm i mem lt j step
    apply Set.mem_of_mem_of_subset _ (assm i mem)
    have step' : j ∈ nfa[i]?.εStep := by
      simp [getElem?_pos nfa i lt, Option.εStep, step]
    exact NFA.εClosure.step step' .base

theorem εClosureTR_spec {i : Fin nfa.nodes.size} {inBounds : nfa.inBounds} :
  ∀ j, (εClosureTR nfa inBounds .empty #[i]).get j ↔ j.val ∈ nfa.εClosure i := by
  let inv (visited : NodeSet nfa.nodes.size) (stack : Array (Fin nfa.nodes.size)) : Prop :=
    (visited.get i ∨ i ∈ stack) ∧
    (∀ i j, visited.get i → j.val ∈ nfa[i].εStep → visited.get j ∨ j ∈ stack) ∧
    (∀ j, (visited.get j ∨ j ∈ stack) → j.val ∈ nfa.εClosure i)

  let rec go (visited : NodeSet nfa.nodes.size) (stack : Array (Fin nfa.nodes.size))
    (inv₀ : inv visited stack) : inv (εClosureTR nfa inBounds visited stack) #[] := by
    unfold εClosureTR
    split
    case inl hemp =>
      have : stack = #[] := (Array.isEmpty_iff).mp hemp
      exact this ▸ inv₀
    case inr hemp =>
      set n := stack.back' hemp with hn
      set stack' := stack.pop with hs'
      have : stack.pop.size < stack.size :=
        Array.lt_size_of_pop_of_not_empty _ hemp
      cases hvis : visited.get n with
      | true =>
        simp [hvis]
        have inv' : inv visited stack.pop := by
          apply And.intro
          . cases inv₀.1 with
            | inl vis => exact Or.inl vis
            | inr stk =>
              cases Nat.decEq i n with
              | isTrue eq =>
                have : i = n := Fin.eq_of_val_eq eq
                exact Or.inl (this ▸ hvis)
              | isFalse neq =>
                have : i ≠ n := Fin.ne_of_val_ne neq
                exact Or.inr (Array.mem_pop _ _ _ stk this)
          . apply And.intro
            . intro i j mem step
              cases inv₀.2.1 i j mem step with
              | inl vis => exact Or.inl vis
              | inr stk =>
                cases decEq j n with
                | isTrue eq => exact Or.inl (eq ▸ hvis)
                | isFalse neq => exact Or.inr (Array.mem_pop _ _ _ stk neq)
            . intro j mem
              cases mem with
              | inl vis => exact inv₀.2.2 j (.inl vis)
              | inr stk =>
                have : j ∈ stack := Array.mem_of_mem_pop _ _ stk
                exact inv₀.2.2 j (.inr this)
        have ih := go visited stack.pop inv'
        simp at ih
        exact ih
      | false =>
        have : (visited.set n).count_unset < visited.count_unset :=
          visited.lt_count_unset n.isLt (by simp [hvis])
        have inBounds' := inBounds n
        simp [hvis]
        split
        next next eqEps =>
          have h : next < nfa.nodes.size := by
            rw [hn] at inBounds'
            simp [eqEps, Node.inBounds] at inBounds'
            exact inBounds'

          set stack'' := stack'.push ⟨next, h⟩ with hs''
          have inv' : inv (visited.set n) stack'' := by
            apply And.intro
            . cases inv₀.1 with
              | inl vis => simp [NodeSet.get_set_set vis]
              | inr stk =>
                cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
                | inl stk => exact Or.inr ((Array.mem_push _ _ _).mpr (.inl stk))
                | inr eq => simp [hn, eq]
            . apply And.intro
              . intro i j mem step
                rw [NodeSet.get_set] at mem
                split at mem
                case inl eq =>
                  simp [eq.symm, eqEps, Node.εStep] at step
                  exact Or.inr ((Array.mem_push _ _ _).mpr (.inr (Fin.eq_of_val_eq step)))
                case inr neq =>
                  cases inv₀.2.1 i j mem step with
                  | inl vis => simp [NodeSet.get_set_set vis]
                  | inr stk =>
                    cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
                    | inl stk => exact Or.inr ((Array.mem_push _ _ _).mpr (.inl stk))
                    | inr eq => simp [hn, eq]
              . intro j mem
                cases mem with
                | inl vis =>
                  rw [NodeSet.get_set] at vis
                  split at vis
                  case inl eq =>
                    rw [←eq]
                    exact inv₀.2.2 n (.inr (Array.mem_back' hemp))
                  case inr _ => exact inv₀.2.2 j (.inl vis)
                | inr stk =>
                  cases (Array.mem_push _ _ _).mp stk with
                  | inl stk =>
                    have : j ∈ stack := Array.mem_of_mem_pop _ _ stk
                    exact inv₀.2.2 j (.inr this)
                  | inr eq =>
                    simp [eq]
                    have : n.val ∈ nfa.εClosure i := inv₀.2.2 n (.inr (Array.mem_back' hemp))
                    exact εClosure_snoc n.isLt this (by simp [Node.εStep, eqEps])
          have ih := go (visited.set n) stack'' inv'
          simp at ih
          exact ih
        next next₁ next₂ eqSplit =>
          rw [hn] at inBounds'
          simp [eqSplit, Node.inBounds] at inBounds'
          have h₁ : next₁ < nfa.nodes.size := inBounds'.left
          have h₂ : next₂ < nfa.nodes.size := inBounds'.right

          set stack'' := (stack'.push ⟨next₁, h₁⟩).push ⟨next₂, h₂⟩ with hs''
          have inv' : inv (visited.set n) stack'' := by
            apply And.intro
            . cases inv₀.1 with
              | inl vis => simp [NodeSet.get_set_set vis]
              | inr stk =>
                cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
                | inl stk =>
                  apply Or.inr
                  apply (Array.mem_push _ _ _).mpr
                  apply Or.inl
                  apply (Array.mem_push _ _ _).mpr
                  exact Or.inl stk
                | inr eq => simp [hn, eq]
            . apply And.intro
              . intro i j mem step
                rw [NodeSet.get_set] at mem
                split at mem
                case inl eq =>
                  simp [eq.symm, eqSplit, Node.εStep] at step
                  cases step with
                  | inl eq₁ =>
                    apply Or.inr
                    apply (Array.mem_push _ _ _).mpr
                    apply Or.inl
                    apply (Array.mem_push _ _ _).mpr
                    apply Or.inr
                    apply Fin.eq_of_val_eq
                    exact eq₁
                  | inr eq₂ =>
                    apply Or.inr
                    apply (Array.mem_push _ _ _).mpr
                    apply Or.inr
                    apply Fin.eq_of_val_eq
                    exact eq₂
                case inr neq =>
                  cases inv₀.2.1 i j mem step with
                  | inl vis => simp [NodeSet.get_set_set vis]
                  | inr stk =>
                    cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
                    | inl stk =>
                      apply Or.inr
                      apply (Array.mem_push _ _ _).mpr
                      apply Or.inl
                      apply (Array.mem_push _ _ _).mpr
                      exact Or.inl stk
                    | inr eq => simp [hn, eq]
              . intro j mem
                cases mem with
                | inl vis =>
                  rw [NodeSet.get_set] at vis
                  split at vis
                  case inl eq =>
                    rw [←eq]
                    exact inv₀.2.2 n (.inr (Array.mem_back' hemp))
                  case inr _ => exact inv₀.2.2 j (.inl vis)
                | inr stk =>
                  cases (Array.mem_push _ _ _).mp stk with
                  | inl stk =>
                    cases (Array.mem_push _ _ _).mp stk with
                    | inl stk =>
                      have : j ∈ stack := Array.mem_of_mem_pop _ _ stk
                      exact inv₀.2.2 j (.inr this)
                    | inr eq =>
                      simp [eq]
                      have : n.val ∈ nfa.εClosure i := inv₀.2.2 n (.inr (Array.mem_back' hemp))
                      exact εClosure_snoc n.isLt this (by simp [Node.εStep, eqSplit])
                  | inr eq =>
                    simp [eq]
                    have : n.val ∈ nfa.εClosure i := inv₀.2.2 n (.inr (Array.mem_back' hemp))
                    exact εClosure_snoc n.isLt this (by simp [Node.εStep, eqSplit])
          have ih := go (visited.set n) stack'' inv'
          simp at ih
          exact ih
        next hne₁ hne₂ =>
          have inv' : inv (visited.set n) stack.pop := by
            apply And.intro
            . cases inv₀.1 with
              | inl vis =>
                rw [NodeSet.get_set_set vis]
                simp
              | inr stk =>
                cases Array.mem_pop_or_eq_of_mem _ _ hemp stk with
                | inl stk => exact Or.inr stk
                | inr eq => simp [hn, eq]
            . apply And.intro
              . intro i j mem step
                rw [NodeSet.get_set] at mem
                split at mem
                case inl eq => simp [eq.symm, Node.εStep] at step
                case inr neq =>
                  have := inv₀.2.1 i j mem step
                  cases this with
                  | inl vis => simp [NodeSet.get_set_set vis]
                  | inr stk =>
                    cases decEq j n with
                    | isTrue eq => simp [eq]
                    | isFalse neq =>
                      apply Or.inr
                      apply Array.mem_pop _ _ _ stk neq
              . intro j mem
                cases mem with
                | inl vis =>
                  cases decEq j n with
                  | isTrue eq =>
                    simp [eq]
                    have : n ∈ stack := Array.mem_back' hemp
                    exact inv₀.2.2 n (.inr this)
                  | isFalse neq =>
                    rw [NodeSet.get_set_ne] at vis
                    . exact inv₀.2.2 j (.inl vis)
                    . intro h
                      exact neq (Fin.eq_of_val_eq h).symm
                | inr stk =>
                  have : j ∈ stack := Array.mem_of_mem_pop _ _ stk
                  exact inv₀.2.2 j (.inr this)
          have ih := go (visited.set n) stack.pop inv'
          simp at ih
          exact ih

  have inv₀ : inv .empty #[i] := by
    simp [inv]
    exact .base
  let ⟨h₁, h₂, h₃⟩ := go .empty #[i] inv₀
  simp at h₁ h₂ h₃
  intro j
  apply Iff.intro
  . exact h₃ j
  . intro h
    let S := { j | ∃ j', (εClosureTR nfa inBounds .empty #[i]).get j' ∧ j = j'.val }
    have mem : i.val ∈ S := by
      simp
      exact ⟨i, h₁, rfl⟩
    have : ∀ j ∈ S, (_ : j < nfa.nodes.size) → ∀ k ∈ nfa[j].εStep, k ∈ S := by
      intro j mem _ k step
      simp at mem
      let ⟨j', h₄, h₅⟩ := mem
      simp [h₅] at step
      have klt : k < nfa.nodes.size := lt_of_inBounds_of_εStep inBounds step
      have := h₂ j' ⟨k, klt⟩ h₄ step
      simp
      exact ⟨⟨k, klt⟩, this, rfl⟩

    have := mem_εStep_iff_εClosure_sub.mp this i mem
    have := Set.mem_of_mem_of_subset h this
    simp at this
    let ⟨j', h₄, h₅⟩ := this
    have : j = j' := Fin.eq_of_val_eq h₅
    exact this ▸ h₄
termination_by go _ => (visited.count_unset, stack.size)

theorem charStepTR_spec {nfa : NFA} {inBounds : nfa.inBounds}
  {init : NodeSet nfa.nodes.size} {k : Fin nfa.nodes.size} :
  (charStepTR nfa inBounds c init).get k ↔
  k.val ∈ nfa.stepSet { j | ∃ j', init.get j' ∧ j = j'.val } c := by
  let inv (accum : NodeSet nfa.nodes.size) (i : Nat) : Prop :=
    ∀ k, accum.get k ↔ k.val ∈ nfa.stepSet { j | ∃ j', init.get j' ∧ j'.val < i ∧ j = j'.val } c

  let lem (i : Nat) (hlt : i < nfa.nodes.size) :
    { j | ∃ j', init.get j' ∧ j' < i + 1 ∧ j = j'.val } =
    if init.get ⟨i, hlt⟩ then
      { j | ∃ j', init.get j' ∧ j' < i ∧ j = j'.val } ∪ {i}
    else
      { j | ∃ j', init.get j' ∧ j' < i ∧ j = j'.val } := by
    split
    case inl h =>
      apply Set.eq_of_subset_of_subset
      . intro j
        simp
        intro j' mem lt eq
        have : j'.val ≤ i := Nat.le_of_lt_succ lt
        cases Nat.lt_or_eq_of_le this with
        | inl lt' => exact .inr ⟨j', mem, lt', eq⟩
        | inr eq' => exact .inl (eq' ▸ eq)
      . intro j
        simp
        intro h'
        match h' with
        | .inl eq =>
          subst eq
          exact ⟨⟨j, hlt⟩, h, Nat.lt_succ_self _, rfl⟩
        | .inr ⟨j', mem, lt, eq⟩ => exact ⟨j', mem, Nat.lt_trans lt (Nat.lt_succ_self _), eq⟩
    case inr h =>
      apply Set.eq_of_subset_of_subset
      . intro j
        simp
        intro j' mem lt eq
        have : j'.val ≤ i := Nat.le_of_lt_succ lt
        cases Nat.lt_or_eq_of_le this with
        | inl lt' => exact ⟨j', mem, lt', eq⟩
        | inr eq' =>
          have : j' = ⟨i, hlt⟩ := Fin.eq_of_val_eq eq'
          rw [this] at mem
          contradiction
      . intro j
        simp
        intro j' mem lt eq
        exact ⟨j', mem, Nat.lt_trans lt (Nat.lt_succ_self _), eq⟩

  let rec go (accum : NodeSet nfa.nodes.size) (i : Nat) (hle : i ≤ nfa.nodes.size)
    (inv₀ : inv accum i) :
    ∀ k, (charStepTR.go nfa inBounds c init accum i hle).get k ↔
      k.val ∈ nfa.stepSet { j | ∃ j', init.get j' ∧ j = j'.val } c := by
    unfold charStepTR.go
    cases decEq i nfa.nodes.size with
    | isTrue h =>
      simp [h]
      simp [h] at inv₀
      exact inv₀
    | isFalse h =>
      simp [h]
      have hlt : i < nfa.nodes.size := Nat.lt_of_le_of_ne hle h
      cases hset : init.get ⟨i, hlt⟩ with
      | true =>
        simp
        split
        next c' next hn =>
          split
          case inl eq =>
            have : next < nfa.nodes.size := by
              have := inBounds ⟨i, hlt⟩
              simp [Node.inBounds, hn] at this
              exact this
            set εCls := εClosureTR nfa inBounds .empty #[⟨next, this⟩]
            set accum' := accum.merge εCls
            have inv' : inv accum' (i + 1) := by
              simp [lem i hlt, hset]
              simp [stepSet_insert_distrib, NodeSet.merge_get]
              intro k
              apply Iff.or
              . exact inv₀ k
              . rw [εClosureTR_spec k]
                simp [NFA.stepSet, getElem?_pos nfa i hlt, hn, Option.charStep, Node.charStep, eq]
                simp [NFA.εClosureSet]
            exact go accum' (i + 1) hlt inv'
          case inr neq =>
            have inv' : inv accum (i + 1) := by
              simp [lem i hlt, hset]
              have : nfa.stepSet {i} c = ∅ := by
                simp [NFA.stepSet, getElem?_pos nfa i hlt, hn, Option.charStep, Node.charStep, neq]
              simp [stepSet_insert_distrib, this]
              exact inv₀
            exact go accum (i + 1) hlt inv'
        next hn =>
          have inv' : inv accum (i + 1) := by
            simp [lem i hlt, hset]
            have : nfa.stepSet {i} c = ∅ := by
              simp [NFA.stepSet, getElem?_pos nfa i hlt, hn, Option.charStep, Node.charStep]
            simp [stepSet_insert_distrib, this]
            exact inv₀
          exact go accum (i + 1) hlt inv'
      | false =>
        simp
        have inv' : inv accum (i + 1) := by
          simp [lem i hlt, hset]
          exact inv₀
        exact go accum (i + 1) hlt inv'

  have inv₀ : inv .empty 0 := by simp [inv, Nat.not_lt_zero]
  apply go .empty 0 (Nat.zero_le _) inv₀
termination_by go _ => nfa.nodes.size - i

def matchList (nfa : NFA) (inBounds : nfa.inBounds) (cs : List Char) : Bool :=
  let ns := εClosureTR nfa inBounds .empty #[nfa.start]
  let ns := go nfa inBounds cs ns
  -- This assumes that the first node is the accepting node
  ns.get ⟨0, nfa.zero_lt_size⟩
where
  go (nfa : NFA) (inBounds : nfa.inBounds) (cs : List Char) (ns : NodeSet nfa.nodes.size) :
    NodeSet nfa.nodes.size :=
    List.foldl (fun ns c => charStepTR nfa inBounds c ns) ns cs

theorem matchList.go_eq_foldl_stepSet {nfa : NFA} {ns : NodeSet nfa.nodes.size}
  {inBounds : nfa.inBounds} {cs : List Char} :
  ∀ j, (go nfa inBounds cs ns).get j ↔
    j.val ∈ List.foldl nfa.stepSet { i | ∃ i', ns.get i' ∧ i = i'.val } cs := by
  induction cs generalizing ns with
  | nil =>
    simp [go]
    intro j
    apply Iff.intro
    . intro h
      exact ⟨j, h, rfl⟩
    . intro h
      let ⟨j', h₁, h₂⟩ := h
      rw [Fin.eq_of_val_eq h₂, h₁]
  | cons c cs ih =>
    simp [go]
    unfold go at ih
    set ns' := charStepTR nfa inBounds c ns
    have spec : ∀ k, ns'.get k ↔ k.val ∈ nfa.stepSet { i | ∃ i', ns.get i' ∧ i = i'.val } c := by
      intro k
      exact charStepTR_spec
    intro j
    rw [ih j]
    congr!
    apply Set.eq_of_subset_of_subset
    . intro i
      simp
      intro i' mem eq
      exact eq ▸ (spec i').mp mem
    . intro i mem
      simp
      have lt : i < nfa.nodes.size := lt_of_inBounds_of_stepSet inBounds mem
      have := (spec ⟨i, lt⟩).mpr mem
      exact ⟨⟨i, lt⟩, this, rfl⟩

theorem match.go_eq_matchList.go {nfa : NFA} {inBounds : nfa.inBounds} {ns : NodeSet nfa.nodes.size}
  {it : String.Iterator} {cs cs' : List Char} (v : it.ValidFor cs cs') :
  NFA.match.go nfa inBounds it ns = matchList.go nfa inBounds cs' ns := by
  induction cs' generalizing it cs ns with
  | nil =>
    unfold NFA.match.go matchList.go
    have : it.atEnd := v.atEnd.mpr rfl
    simp [this]
  | cons c cs' ih =>
    unfold NFA.match.go matchList.go
    have : ¬ it.atEnd := by
      intro h
      have := v.atEnd.mp h
      contradiction
    simp [this]
    have : it.curr = c := by
      simp [v.curr]
    simp [this]
    exact ih v.next

theorem evalFrom_iff_matchList {nfa : NFA} {inBounds : nfa.inBounds} {cs : List Char} :
  0 ∈ nfa.evalFrom {nfa.start.val} cs ↔ matchList nfa inBounds cs := by
  unfold NFA.evalFrom matchList
  simp [matchList.go_eq_foldl_stepSet, εClosureTR_spec]
  have :
    {i | ∃ i' : Fin nfa.nodes.size, i'.val ∈ NFA.εClosure nfa nfa.start.val ∧ i = i'.val} =
    nfa.εClosureSet {nfa.start.val} := by
    simp [NFA.εClosureSet]
    apply Set.eq_of_subset_of_subset
    . intro i mem
      simp at mem
      let ⟨i', mem', eq⟩ := mem
      exact eq ▸ mem'
    . intro i mem
      have lt : i < nfa.nodes.size := lt_of_inBounds_of_εClosure inBounds nfa.start.isLt mem
      simp
      exact ⟨⟨i, lt⟩, mem, rfl⟩
  rw [this]

end NFA.VM

namespace NFA

theorem match_eq_matchList {nfa : NFA} {inBounds : nfa.inBounds} {s : String} :
  NFA.match nfa inBounds s = NFA.VM.matchList nfa inBounds s.data := by
  unfold NFA.match NFA.VM.matchList
  simp
  rw [NFA.VM.match.go_eq_matchList.go s.validFor_mkIterator]

-- Correctness of the VM interpreter
theorem NFA.match_iff_regex_matches {s : String} (eq : compile r = nfa) :
  nfa.match (compile.inBounds eq) s ↔ r.matches s := by
  apply Iff.intro
  . intro m
    have : NFA.VM.matchList nfa (compile.inBounds eq) s.data :=
      match_eq_matchList ▸ m
    have := NFA.VM.evalFrom_iff_matchList.mpr this
    exact matches_of_evalFrom' eq this
  . intro m
    have := evalFrom_of_matches' eq m
    have := (NFA.VM.evalFrom_iff_matchList (inBounds := compile.inBounds eq)).mp this
    exact match_eq_matchList ▸ this

end NFA

namespace NFAa.VM

open NFA.VM

theorem mem_εStep_iff_εClosure_sub {nfa : NFAa} {S : Set Nat} :
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

def εClosureTRa_spec.inv (nfa : NFAa) (i : Fin nfa.nodes.size)
  (visited : NodeSet nfa.nodes.size) (stack : Array (Fin nfa.nodes.size)) : Prop :=
  (visited.get i ∨ i ∈ stack) ∧
  (∀ i j, visited.get i → j.val ∈ nfa[i].εStep → visited.get j ∨ j ∈ stack) ∧
  (∀ j, (visited.get j ∨ j ∈ stack) → j.val ∈ nfa.εClosure i)

theorem εClosureTRa_spec.case_visited (inv₀ : inv nfa i visited stack)
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

theorem εClosureTRa_spec.case_epsilon (inv₀ : inv nfa i visited stack)
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

theorem εClosureTRa_spec.case_split (inv₀ : inv nfa i visited stack)
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

theorem εClosureTRa_spec.case_else (inv₀ : inv nfa i visited stack)
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
theorem εClosureTRa_spec.go (nfa : NFAa) (i : Fin nfa.nodes.size) {visited stack}
  (inv₀ : inv nfa i visited stack) :
  inv nfa i (εClosureTRa nfa visited stack) #[] := by
  unfold εClosureTRa
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
termination_by _ => (visited.count_unset, stack.size)

theorem εClosureTRa_spec {nfa : NFAa} {i : Fin nfa.nodes.size} :
  ∀ j, (εClosureTRa nfa .empty #[i]).get j ↔ j.val ∈ nfa.εClosure i := by
  have inv₀ : εClosureTRa_spec.inv nfa i .empty #[i] := by
    simp [εClosureTRa_spec.inv]
    exact .base
  have ⟨h₁, h₂, h₃⟩ := εClosureTRa_spec.go nfa i inv₀
  simp at h₁ h₂ h₃
  intro j
  apply Iff.intro
  . exact h₃ j
  . intro h
    let S := { j | ∃ lt : j < nfa.nodes.size, (εClosureTRa nfa .empty #[i]).get ⟨j, lt⟩ }
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

def charStepTRa_spec.inv (nfa : NFAa) (c : Char) (init : NodeSet nfa.nodes.size)
  (accum : NodeSet nfa.nodes.size) (i : Nat) : Prop :=
  ∀ k, accum.get k ↔ k.val ∈ nfa.stepSet { j | j < i ∧ ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } c

theorem charStepTRa_spec.lem (nfa : NFAa) (init : NodeSet nfa.nodes.size)
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

theorem charStepTRa_spec.go (nfa : NFAa) (c : Char) (init : NodeSet nfa.nodes.size)
  (accum : NodeSet nfa.nodes.size) (i : Nat) (hle : i ≤ nfa.nodes.size)
  (inv₀ : inv nfa c init accum i) :
  ∀ k, ((charStepTRa.go nfa c init accum i hle)).get k ↔
  k.val ∈ nfa.stepSet { j | ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } c := by
  unfold charStepTRa.go
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
              simp [εClosureTRa_spec k] at hset
              simp [stepSet, εClosureSet]
              refine ⟨next, ?_, hset⟩
              simp [charStep, get_eq_nodes_get, NFA.Node.charStep, hn, eqc, hlt]
          . intro hset
            simp [NodeSet.merge_get]
            cases hset with
            | inl hset => exact .inl ((inv₀ k).mpr hset)
            | inr hset =>
              apply Or.inr
              simp [εClosureTRa_spec k]
              simp [stepSet, εClosureSet, charStep, get_eq_nodes_get, NFA.Node.charStep, hn, eqc, hlt] at hset
              exact hset
        case inr nec =>
          have : nfa.stepSet {i} c = ∅ := by
            simp [stepSet, charStep, NFA.Node.charStep, get_eq_nodes_get, hn, nec]
          simp [this]
          exact inv₀
      next hn =>
        have : nfa.stepSet {i} c = ∅ := by
          simp [stepSet, charStep, NFA.Node.charStep, get_eq_nodes_get, hn]
        simp [this]
        exact inv₀
    case inr hset =>
      simp [inv, lem nfa init i hlt, hset]
      exact inv₀
termination_by _ => nfa.nodes.size - i

theorem charStepTRa_spec (nfa : NFAa) (c : Char) (init : NodeSet nfa.nodes.size) :
  ∀ k, (charStepTRa nfa c init).get k ↔
  k.val ∈ nfa.stepSet { j | ∃ h : j < nfa.nodes.size, init.get ⟨j, h⟩ } c := by
  have inv₀ : charStepTRa_spec.inv nfa c init .empty 0 := by
    simp [charStepTRa_spec.inv, Nat.not_lt_zero]
  exact charStepTRa_spec.go nfa c init .empty 0 (Nat.zero_le _) inv₀

def matchList (nfa : NFAa) (cs : List Char) : Bool :=
  let ns := εClosureTRa nfa .empty #[nfa.start]
  let ns := go nfa cs ns
  -- This assumes that the first node is the accepting node
  ns.get ⟨0, nfa.zero_lt_size⟩
where
  go (nfa : NFAa) (cs : List Char) (ns : NodeSet nfa.nodes.size) : NodeSet nfa.nodes.size :=
    List.foldl (fun ns c => charStepTRa nfa c ns) ns cs

theorem matchList.go_eq_foldl_stepSet {nfa : NFAa} {ns : NodeSet nfa.nodes.size} {cs : List Char} :
  ∀ j, (go nfa cs ns).get j ↔
    j.val ∈ List.foldl nfa.stepSet { i | ∃ h : i < nfa.nodes.size, ns.get ⟨i, h⟩ } cs := by
  induction cs generalizing ns with
  | nil => simp [go]
  | cons c cs ih =>
    simp [go]
    unfold go at ih
    have spec := charStepTRa_spec nfa c ns
    intro j
    rw [ih j]
    congr!
    simp [spec]
    apply Set.eq_of_subset_of_subset
    . intro i
      simp
    . intro i mem
      simp [mem]
      exact lt_of_mem_stepSet mem

theorem evalFrom_iff_matchList {nfa : NFAa} {cs : List Char} :
  0 ∈ nfa.evalFrom {nfa.start.val} cs ↔ matchList nfa cs := by
  unfold NFAa.evalFrom matchList
  simp [matchList.go_eq_foldl_stepSet, εClosureTRa_spec]
  congr! 2
  simp [εClosureSet]
  apply Set.eq_of_subset_of_subset
  . intro i mem
    simp
    exact ⟨lt_of_εClosure_right nfa.start.isLt mem, mem⟩
  . intro i mem
    simp at mem
    exact mem.right

theorem match.go_eq_matchList.go {nfa : NFAa} {ns : NodeSet nfa.nodes.size}
  {it : String.Iterator} {cs cs' : List Char} (v : it.ValidFor cs cs') :
  NFAa.match.go nfa it ns = matchList.go nfa cs' ns := by
  induction cs' generalizing it cs ns with
  | nil =>
    unfold NFAa.match.go matchList.go
    have : it.atEnd := v.atEnd.mpr rfl
    simp [this]
  | cons c cs' ih =>
    unfold NFAa.match.go matchList.go
    have : ¬ it.atEnd := by
      intro h
      have := v.atEnd.mp h
      contradiction
    simp [this]
    have : it.curr = c := by
      simp [v.curr]
    simp [this]
    exact ih v.next

theorem match_eq_matchList {nfa : NFAa} {s : String} :
  nfa.match s ↔ matchList nfa s.data := by
  unfold NFAa.match matchList
  simp
  rw [match.go_eq_matchList.go s.validFor_mkIterator]

theorem evalFrom_iff_match {nfa : NFAa} {s : String} :
  nfa.match s ↔ 0 ∈ nfa.evalFrom {nfa.start.val} s.data := by
  rw [match_eq_matchList, evalFrom_iff_matchList]

theorem match_iff_regex_matches (eq : NFAa.compile r = nfa) :
  nfa.match s ↔ r.matches s := by
  rw [evalFrom_iff_match]
  exact ⟨matches_of_compile_evalFrom eq, evalFrom_of_compile_matches eq⟩

end NFAa.VM
