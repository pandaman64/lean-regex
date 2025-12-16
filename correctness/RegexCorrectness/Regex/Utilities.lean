import Regex.Regex.Utilities
import RegexCorrectness.Regex.Matches
import RegexCorrectness.Regex.Captures

set_option autoImplicit false

open String (Pos Slice)

namespace Regex

variable {re : Regex} {haystack : String} {slice : Slice}

theorem find_str_eq_some (h : re.find haystack = .some slice) :
  slice.str = haystack := by
  grind [Matches.str_eq_of_next?_some, Option.map_eq_some_iff, find]

theorem captures_of_find_some  (h : re.find haystack = .some slice)
  (isr : re.IsSearchRegex) :
  Matches.Spec isr haystack haystack.startValidPosPlusOne slice (find_str_eq_some h) := by
  simp only [find, Option.map_eq_some_iff, Prod.exists, exists_and_right, exists_eq_right] at h
  have ⟨_, h⟩ := h
  exact Matches.captures_of_next?_some h isr

theorem captures_of_mem_findAll.go {m : Matches haystack} {accum : Array Slice} (isr : m.regex.IsSearchRegex)
  (inv : ∀ slice ∈ accum, ∃ startPos eq, Matches.Spec isr haystack startPos slice eq) :
  ∀ slice ∈ findAll.go haystack m accum, ∃ startPos eq, Matches.Spec isr haystack startPos slice eq := by
  induction m, accum using findAll.go.induct with
  | case1 m accum slice m' h ih =>
    -- next match is found
    rw [findAll.go, h]
    have eq' : m'.regex = m.regex := Matches.regex_eq_of_next?_some h
    have spec : ∃ startPos eq, Matches.Spec isr haystack startPos slice eq := ⟨_, _, m.captures_of_next?_some h isr⟩
    grind [Matches.regex_eq_of_next?_some]
  | case2 m accum h =>
    -- next match is not found
    rw [findAll.go, h]
    exact inv

theorem captures_of_mem_findAll (mem : slice ∈ re.findAll haystack) (isr : re.IsSearchRegex) :
  ∃ startPos eq, Matches.Spec isr haystack startPos slice eq := by
  dsimp [Regex.findAll] at mem
  have eq : (re.matches haystack).regex = re := rfl
  exact captures_of_mem_findAll.go (eq ▸ isr) (by grind) slice mem

theorem captures_of_capture_some {captured} (h : re.capture haystack = .some captured) (isr : re.IsSearchRegex) :
  captured.Spec isr haystack haystack.startValidPosPlusOne := by
  simp [Regex.capture] at h
  have ⟨_, h⟩ := h
  exact Captures.captures_of_next?_some h isr

theorem captures_of_mem_captureAll.go {captures : Captures haystack} {accum : Array (CapturedGroups haystack)} (isr : captures.regex.IsSearchRegex)
  (inv : ∀ captured ∈ accum, ∃ startPos, CapturedGroups.Spec isr haystack startPos captured) :
  ∀ captured ∈ captureAll.go haystack captures accum, ∃ startPos, CapturedGroups.Spec isr haystack startPos captured := by
  induction captures, accum using captureAll.go.induct with
  | case1 captures accum groups captures' h ih =>
    -- next capture is found
    rw [captureAll.go, h]
    -- simp
    have eq' : captures'.regex = captures.regex := Captures.regex_eq_of_next?_some h
    have spec : ∃ startPos, CapturedGroups.Spec isr haystack startPos groups := ⟨_, captures.captures_of_next?_some h isr⟩
    grind
  | case2 captures accum next?_none =>
    -- next capture is not found
    rw [captureAll.go, next?_none]
    exact inv

theorem captures_of_mem_captureAll {captured} (mem : captured ∈ re.captureAll haystack) (isr : re.IsSearchRegex) :
  ∃ startPos, CapturedGroups.Spec isr haystack startPos captured := by
  dsimp [Regex.captureAll] at mem
  have eq : (re.captures haystack).regex = re := rfl
  exact captures_of_mem_captureAll.go (eq ▸ isr) (by grind) captured mem

end Regex
