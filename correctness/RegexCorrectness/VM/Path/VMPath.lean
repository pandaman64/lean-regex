import Regex.Data.SparseSet
import RegexCorrectness.VM.Path.EpsilonClosure
import RegexCorrectness.VM.Path.CharStep

set_option autoImplicit false

open Regex.Data (Span SparseSet Vec)
open Regex (NFA)
open String (Pos Iterator)

namespace Regex.NFA

inductive VMPath (nfa : NFA) (wf : nfa.WellFormed) : Span → Fin nfa.nodes.size → List (Nat × Pos) → Prop where
  | init {l r i update} (cls : nfa.εClosure' ⟨l, [], r⟩ ⟨nfa.start, wf.start_lt⟩ i update) :
    VMPath nfa wf ⟨l, [], r⟩  i update
  | more {i j k span c r' update₁ update₂} (prev : VMPath nfa wf span i update₁) (h : span.r = c :: r')
    (step : nfa.CharStep span.l span.m c r' i j) (cls : nfa.εClosure' span.next j k update₂) :
    VMPath nfa wf span.next k (update₁ ++ update₂)

namespace VMPath

theorem eq_or_nfaPath {nfa : NFA} {wf span i update} (path : nfa.VMPath wf span i update) :
  ∃ l r,
    (span = ⟨l, [], r⟩ ∧ i.val = nfa.start ∧ update = []) ∨
    nfa.Path 0 nfa.start ⟨l, [], r⟩ i span update := by
  induction path with
  | @init l r i update cls =>
    simp [εClosure'_iff_path nfa wf] at cls
    exists l, r
    cases cls with
    | inl h => simp [←h.1, h.2]
    | inr cls => simp [cls]
  | @more i j k span c r' update₁ update₂ prev h step cls ih =>
    have path₂ : nfa.Path 0 i ⟨span.l, span.m, c :: r'⟩ k ⟨span.l, c :: span.m, r'⟩ update₂ := by
      simp [CharStep] at step
      simp [εClosure'_iff_path nfa wf] at cls
      match cls with
      | .inl ⟨eqk, equpdate⟩ =>
        subst k update₂
        exact .last step
      | .inr path =>
        simp [Span.next_eq h] at path
        exact Path.more step path

    have ⟨l, r, h'⟩ := ih
    match h' with
    | .inl ⟨eqspan, eqi, equpdate⟩ =>
      simp [Span.next_eq h]
      simp [eqspan, eqi] at path₂ h
      simp [eqspan, equpdate]
      refine ⟨l, c :: r', path₂⟩
    | .inr path₁ =>
      have : span = ⟨span.l, span.m, c :: r'⟩ :=
        calc
          _ = (⟨span.l, span.m, span.r⟩ : Span) := rfl
          _ = _ := by simp [h]
      rw [this] at path₁
      simp [Span.next_eq h]
      exact ⟨l, r, path₁.trans path₂⟩

theorem nfaPath_of_ne {nfa : NFA} {wf span i update} (path : nfa.VMPath wf span i update)
  (ne : i.val ≠ nfa.start):
  ∃ l r, nfa.Path 0 nfa.start ⟨l, [], r⟩ i span update := by
  have ⟨l, r, h⟩ := eq_or_nfaPath path
  simp [ne] at h
  exact ⟨l, r, h⟩

end VMPath

end Regex.NFA

namespace Regex.VM

structure SearchState' (nfa : NFA) where
  states : SparseSet nfa.nodes.size
  updates : Vec (List (Nat × Pos)) nfa.nodes.size

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
def WriteUpdate {nfa : NFA} (i : Fin nfa.nodes.size) : Prop :=
  match nfa[i] with
  | .done | .char _ _ | .sparse _ _ => True
  | _ => False

/--
All states in `next.state` have a corresponding path from `nfa.start` to the state where the span
ends at `it`, and their updates are written to `next.updates` when necessary.
-/
def SearchState'.Inv (nfa : NFA) (wf : nfa.WellFormed) (it : Iterator) (next : SearchState' nfa) : Prop :=
  ∀ i ∈ next.states,
    ∃ span update,
      span.iterator = it ∧
      nfa.VMPath wf span i update ∧
      (WriteUpdate i → next.updates[i] = update)

theorem SearchState'.Inv.of_empty {nfa wf it} {next : SearchState' nfa} (h : next.states.isEmpty) :
  next.Inv nfa wf it := by
  intro i mem
  exact (SparseSet.not_mem_of_isEmpty h mem).elim

end Regex.VM

theorem Regex.NFA.CharStep.write_update {nfa : NFA} {l m c r i j}
  (step : nfa.CharStep l m c r i j) : Regex.VM.WriteUpdate i := by
  cases step <;> simp_all [VM.WriteUpdate]
