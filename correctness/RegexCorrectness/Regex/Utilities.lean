import Regex.Regex.Utilities
-- import RegexCorrectness.Regex.Matches
-- import RegexCorrectness.Regex.Captures
import RegexCorrectness.Regex.Iterators.Captures

open String (Pos)
open Std.Iterators (Iter IterM)

namespace Regex

variable {re : Regex} {haystack : String}

-- theorem captures_of_find_some {positions} (h : re.find haystack = .some positions)
--   (s : re.IsSearchRegex) :
--   Matches.Spec s haystack ⟨0⟩ positions := by
--   simp [Regex.find] at h
--   have ⟨_, h⟩ := h
--   have v := Captures.valid_captures haystack s
--   exact (Matches.captures_of_next?_some h v).2

-- theorem captures_of_mem_findAll.go {m : Matches} {accum : Array Substring}
--   (v : m.Valid) (inv : ∀ str ∈ accum, ∃ startPos, Matches.Spec v.1 m.haystack startPos str) :
--   ∀ str ∈ findAll.go m accum, ∃ startPos, Matches.Spec v.1 m.haystack startPos str := by
--   induction m, accum using findAll.go.induct with
--   | case1 m accum positions m' next_some? ih =>
--     -- next match is found
--     rw [findAll.go, next_some?]
--     simp
--     have regex_eq := Matches.regex_eq_of_next?_some next_some?
--     have haystack_eq := Matches.haystack_eq_of_next?_some next_some?
--     simp [regex_eq, haystack_eq] at ih

--     have ⟨v', spec⟩ := Matches.captures_of_next?_some next_some? v
--     have inv' (str : Substring) (mem : str ∈ accum ∨ str = positions) : ∃ startPos, Matches.Spec v.1 m.haystack startPos str := by
--       cases mem with
--       | inl mem => exact inv str mem
--       | inr eq => exact ⟨m.currentPos, eq ▸ spec⟩
--     exact ih v' inv'
--   | case2 m accum next_none? =>
--     -- next match is not found
--     rw [findAll.go, next_none?]
--     dsimp
--     exact inv

-- theorem captures_of_mem_findAll {positions} (mem : positions ∈ re.findAll haystack)
--   (s : re.IsSearchRegex) :
--   ∃ startPos, Matches.Spec s haystack startPos positions := by
--   simp [Regex.findAll] at mem
--   have v := Matches.vaild_matches haystack s
--   exact captures_of_mem_findAll.go v (by simp) positions mem

-- theorem captures_of_capture_some {captured} (h : re.capture haystack = .some captured)
--   (s : re.IsSearchRegex) :
--   captured.Spec s haystack ⟨0⟩ := by
--   simp [Regex.capture] at h
--   have ⟨_, h⟩ := h
--   have v := Captures.valid_captures haystack s
--   exact (Captures.captures_of_next?_some h v).2

-- theorem captures_of_mem_captureAll.go {captures : Captures} {accum : Array CapturedGroups}
--   (v : captures.Valid) (inv : ∀ captured ∈ accum, ∃ startPos, CapturedGroups.Spec v.1 captures.haystack startPos captured) :
--   ∀ captured ∈ captureAll.go captures accum, ∃ startPos, CapturedGroups.Spec v.1 captures.haystack startPos captured := by
--   induction captures, accum using captureAll.go.induct with
--   | case1 captures accum groups captures' next?_some ih =>
--     -- next capture is found
--     rw [captureAll.go, next?_some]
--     simp
--     have regex_eq := Captures.regex_eq_of_next?_some next?_some
--     have haystack_eq := Captures.haystack_eq_of_next?_some next?_some
--     simp [regex_eq, haystack_eq] at ih

--     have ⟨v', spec⟩ := Captures.captures_of_next?_some next?_some v
--     have inv' (captured : CapturedGroups) (mem : captured ∈ accum ∨ captured = groups) : ∃ startPos, CapturedGroups.Spec v.1 captures.haystack startPos captured := by
--       cases mem with
--       | inl mem => exact inv captured mem
--       | inr eq => exact ⟨captures.currentPos, eq ▸ spec⟩
--     exact ih v' inv'
--   | case2 captures accum next?_none =>
--     -- next capture is not found
--     rw [captureAll.go, next?_none]
--     simp
--     exact inv

#check Std.Iterators.Iter.mem_toList_iff_isPlausibleIndirectOutput
#check Std.Iterators.Iter.isPlausibleIndirectOutput_of_mem_toList
#synth Membership Nat (Array Nat)

#check Std.Iterators.Iter.unattach_toArray_attachWith

-- universe u
-- inductive Iter.IsPlausibleIndirectOutput {α β : Type u} [Std.Iterators.Iterator α Id β] (it : Std.Iterators.Iter (α := α) β) :
--     β → Prop where
--   | direct {out : β} : it.IsPlausibleOutput out →
--       IsPlausibleIndirectOutput it out
--   | indirect {it' : Std.Iterators.Iter (α := α) β} {out : β} : it'.IsPlausibleSuccessorOf it →
--       it'.IsPlausibleIndirectOutput out → IsPlausibleIndirectOutput it out

def captures_attach_spec (regex : Regex) (haystack : String) (s : re.IsSearchRegex) :=
  regex.captures haystack |>.attachWith (fun groups => ∃ startPos, CapturedGroups.Spec s haystack startPos groups) proof
where
  proof (groups : CapturedGroups) (h : (regex.captures haystack).IsPlausibleIndirectOutput groups) : ∃ startPos, CapturedGroups.Spec s haystack startPos groups := by
    -- generalize eq : regex.captures haystack = it at h
    cases h with
    | @direct it groups h => sorry
    | @indirect it' it groups ps pio => sorry

-- theorem spec_of_captures_isPlausibleIndirectOutputAux {re : Regex} {haystack : String} {it : IterM (α := Captures) m CapturedGroups}
--   {bufferSize groups} [Monad m] (s : re.IsSearchRegex) (v : it.internalState.Valid)
--   (pis : it.IsPlausibleIndirectSuccessorOf (re.capturesM haystack m bufferSize)) (pio : it.IsPlausibleIndirectOutput groups) :
--   ∃ startPos, CapturedGroups.Spec s haystack startPos groups := by
--   induction pio with
--   | @direct it out pio => sorry
--   | @indirect it it' out ps pio ih =>
--     have := (IterM.IsPlausibleIndirectSuccessorOf.single ps).trans pis
--     simp [IterM.IsPlausibleSuccessorOf] at ps
--     obtain ⟨step, eq, ps⟩ := ps
--     simp [Std.Iterators.IterStep.successor] at eq
--     sorry

theorem spec_of_mem_captureAllAux {re : Regex} {haystack : String} {it : Iter (α := Captures) CapturedGroups} {groups}
  (s : re.IsSearchRegex) (v : it.internalState.Valid)
  (pis : it.IsPlausibleIndirectSuccessorOf (re.captures haystack)) (mem : groups ∈ it.toArray) :
  ∃ startPos, CapturedGroups.Spec s haystack startPos groups := by
  match eq : it.step with
  | .yield it' groups' h =>
    rw [Iter.toArray_eq_match_step, eq] at mem
    simp at mem
    cases mem with
    | inl eq' => sorry
    | inr mem => exact spec_of_mem_captureAllAux s sorry sorry mem
  | .skip it' h => exact spec_of_mem_captureAllAux s sorry sorry mem
  | .done h => sorry
termination_by it.finitelyManySteps

theorem spec_of_mem_captureAll {groups} (mem : groups ∈ re.captureAll haystack)
  (s : re.IsSearchRegex) :
  ∃ startPos, CapturedGroups.Spec s haystack startPos groups := by
  dsimp [Regex.captureAll] at mem
  exact spec_of_mem_captureAllAux s (Captures.valid_captures haystack s) (.refl (re.captures haystack)) mem
  -- rw [Array.mem_def, Std.Iterators.Iter.toList_toArray] at mem
  -- have h := Std.Iterators.Iter.isPlausibleIndirectOutput_of_mem_toList mem
  -- generalize eq : re.captures haystack = it at h
  -- -- ????
  -- induction h generalizing re with
  -- | @direct it groups po => sorry
  -- | @indirect it' it groups ps pio ih => sorry
  -- -- exact captures_of_mem_captureAll.go v (by simp) captured mem

end Regex
