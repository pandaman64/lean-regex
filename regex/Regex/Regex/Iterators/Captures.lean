import Regex.Regex.Basic
import Regex.Regex.Iterators.CapturedGroups
import Std.Data.Iterators

open String (Pos)
open Std.Iterators (Iter IterM IterStep Iterator Finite toIterM)

namespace Regex

structure Captures where
  regex : Regex
  haystack : String
  bufferSize : Nat
  currentPos : Pos
deriving Repr

namespace Captures

def withPos (self : Captures) (pos : Pos) : Captures :=
  { self with currentPos := pos }

@[simp]
theorem withPos_currentPos (self : Captures) (pos : Pos) : (self.withPos pos).currentPos = pos := rfl

@[simp]
theorem withPos_regex (self : Captures) (pos : Pos) : (self.withPos pos).regex = self.regex := rfl

@[simp]
theorem withPos_haystack (self : Captures) (pos : Pos) : (self.withPos pos).haystack = self.haystack := rfl

@[simp]
theorem withPos_bufferSize (self : Captures) (pos : Pos) : (self.withPos pos).bufferSize = self.bufferSize := rfl

@[simp]
theorem eq_of_withPos_eq (c₁ c₂ : Captures) (p₁ p₂ : Pos) (h : c₁.withPos p₁ = c₂.withPos p₂) : p₁ = p₂ := by
  simp_all [withPos]

@[simp]
theorem withPos_eq_iff (c : Captures) (p₁ p₂ : Pos) : c.withPos p₁ = c.withPos p₂ ↔ p₁ = p₂ := by
  simp [withPos]

def step (self : Captures) : IterStep Captures CapturedGroups :=
  if self.currentPos ≤ self.haystack.endPos then
    match self.regex.captureNextBuf self.bufferSize ⟨self.haystack, self.currentPos⟩ with
    | .some buffer =>
      let groups : CapturedGroups := ⟨self.haystack, buffer.toArray⟩
      match groups.get 0 with
      | .some matched =>
        let nextPos := if self.currentPos < matched.stopPos then
          matched.stopPos
        else
          self.haystack.next self.currentPos
        .yield (self.withPos nextPos) groups
      | .none =>
        -- this should never happen in practice, so we use the same logic as the .none case below to make IsPlausibleStep simple
        .skip (self.withPos (self.haystack.endPos + ⟨1⟩))
    | .none =>
      -- No match left in the haystack, so we skip the rest of the haystack
      .skip (self.withPos (self.haystack.endPos + ⟨1⟩))
  else
    .done

theorem step_yield (c c' : Captures) (groups : CapturedGroups) (h : c.step = .yield c' groups) :
  c.currentPos ≤ c.haystack.endPos ∧
  ∃ buffer, c.regex.captureNextBuf c.bufferSize ⟨c.haystack, c.currentPos⟩ = .some buffer ∧
  groups = ⟨c.haystack, buffer.toArray⟩ ∧
  ∃ matched, groups.get 0 = .some matched ∧
  c' = c.withPos (if c.currentPos < matched.stopPos then matched.stopPos else c.haystack.next c.currentPos) := by
  revert h
  fun_cases step c
  case case1 hle buffer eq groups' matched eq' nextPos =>
    intro h
    simp at h
    simp [←h, hle, eq, groups', eq', nextPos]
  all_goals simp

theorem step_skip (c c' : Captures) (h : c.step = .skip c') :
  c.currentPos ≤ c.haystack.endPos ∧ c' = c.withPos (c.haystack.endPos + ⟨1⟩) := by
  revert h
  fun_cases step c <;> simp_all

theorem step_done (c : Captures) (h : c.step = .done) : c.currentPos > c.haystack.endPos := by
  revert h
  fun_cases step c
  case case4 nle => intro; exact Nat.gt_of_not_le nle
  all_goals simp

def IsPlausibleStep (it : IterM (α := Captures) m CapturedGroups) (step : IterStep (IterM (α := Captures) m CapturedGroups) CapturedGroups) : Prop :=
  match step with
  | .yield it' out =>
    it.internalState.currentPos ≤ it.internalState.haystack.endPos ∧
    ∃ buffer, it.internalState.regex.captureNextBuf it.internalState.bufferSize ⟨it.internalState.haystack, it.internalState.currentPos⟩ = .some buffer ∧
    out = ⟨it.internalState.haystack, buffer.toArray⟩ ∧
    ∃ matched, out.get 0 = .some matched ∧
    it' = toIterM (it.internalState.withPos (if it.internalState.currentPos < matched.stopPos then matched.stopPos else it.internalState.haystack.next it.internalState.currentPos)) m CapturedGroups
  | .skip it' => it.internalState.currentPos ≤ it.internalState.haystack.endPos ∧ it'.internalState = it.internalState.withPos (it.internalState.haystack.endPos + ⟨1⟩)
  | .done => it.internalState.currentPos > it.internalState.haystack.endPos

theorem step_IsPlausibleStep {it : IterM (α := Captures) m CapturedGroups} : IsPlausibleStep it (it.internalState.step.mapIterator (⟨·⟩)) := by
  match h : it.internalState.step with
  | .yield it' out =>
    have ⟨hle, buffer, eq₁, eq₂, matched, eq₃, eq₄⟩ := step_yield it.internalState it' out h
    simp [IsPlausibleStep]
    exact ⟨hle, buffer, eq₁, eq₂, matched, eq₃, by simp [toIterM, eq₄]⟩
  | .skip it' =>
    have ⟨hle, h⟩ := step_skip it.internalState it' h
    simp [IsPlausibleStep, hle, h]
  | .done => simpa [IsPlausibleStep] using step_done it.internalState h

section Iterators

variable {m : Type → Type w} [Pure m]

@[always_inline, inline]
instance: Iterator Captures m CapturedGroups where
  IsPlausibleStep := IsPlausibleStep
  step it := pure ⟨it.internalState.step.mapIterator (⟨·⟩), step_IsPlausibleStep⟩

def measureFun (self : Captures) : Nat := self.haystack.endPos.byteIdx + 1 - self.currentPos.byteIdx

private def finetenessRelation : Std.Iterators.FinitenessRelation Captures m where
  rel := InvImage WellFoundedRelation.rel (fun it => it.internalState.measureFun)
  wf := InvImage.wf _ WellFoundedRelation.wf
  subrelation {it it'} h := by
    simp_wf
    obtain ⟨step, h, h'⟩ := h
    cases step with
    | yield _ out =>
      simp [IterStep.successor] at h
      simp [h, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, IsPlausibleStep] at h'
      obtain ⟨hle, buffer, eq₁, eq₂, matched, eq₃, eq₄⟩ := h'
      simp [toIterM] at eq₄
      simp [measureFun, eq₄]
      refine Nat.sub_lt_sub_left (Nat.succ_le_succ hle) ?_
      split <;> simp_all [String.next, Char.utf8Size_pos]
    | skip _ =>
      simp [IterStep.successor] at h
      simp [h, IterM.IsPlausibleStep, Iterator.IsPlausibleStep, IsPlausibleStep] at h'
      simp [measureFun, h']
      exact Nat.zero_lt_sub_of_lt (Nat.succ_le_succ h'.1)
    | done => simp [IterStep.successor] at h

instance : Finite Captures m := Finite.of_finitenessRelation finetenessRelation

@[always_inline, inline]
instance [Monad n] : Std.Iterators.IteratorCollect Captures m n := .defaultImplementation

@[always_inline, inline]
instance [Monad n] : Std.Iterators.IteratorCollectPartial Captures m n := .defaultImplementation

@[always_inline, inline]
instance [Monad n] : Std.Iterators.IteratorLoop Captures m n := .defaultImplementation

@[always_inline, inline]
instance [Monad m] [Monad n] : Std.Iterators.IteratorLoopPartial Captures m n := .defaultImplementation

end Iterators

end Captures

def capturesM (regex : Regex) (haystack : String) (m : Type → Type w) (bufferSize : Nat := regex.maxTag + 1) [Monad m] : IterM (α := Captures) m CapturedGroups :=
  toIterM ⟨regex, haystack, bufferSize, 0⟩ m CapturedGroups

def captures (regex : Regex) (haystack : String) (bufferSize : Nat := regex.maxTag + 1) : Iter (α := Captures) CapturedGroups :=
  (capturesM regex haystack Id bufferSize).toIter

end Regex
