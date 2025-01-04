import Regex.Regex.Utilities
import RegexCorrectness.Regex.Matches
import RegexCorrectness.Regex.Captures

set_option autoImplicit false

open String (Pos)

namespace Regex

variable {re : Regex} {haystack : String}

theorem captures_of_find_some {positions} (h : re.find haystack = .some positions)
  (s : re.IsSearchRegex) :
  Matches.Spec s haystack positions := by
  simp [Regex.find] at h
  have ⟨_, h⟩ := h
  have v := Captures.valid_captures haystack s
  exact (Matches.captures_of_next?_some h v).2

theorem captures_of_mem_findAll.go {m : Matches} {accum : Array (Pos × Pos)}
  (v : m.Valid) (inv : ∀ positions ∈ accum, Matches.Spec v.1 m.haystack positions) :
  ∀ positions ∈ findAll.go m accum, Matches.Spec v.1 m.haystack positions := by
  induction m, accum using findAll.go.induct with
  | case1 m accum positions m' next_some? ih =>
    -- next match is found
    rw [findAll.go, next_some?]
    simp
    have regex_eq := Matches.regex_eq_of_next?_some next_some?
    have haystack_eq := Matches.haystack_eq_of_next?_some next_some?
    simp [regex_eq, haystack_eq] at ih

    have ⟨v', spec⟩ := Matches.captures_of_next?_some next_some? v
    have inv' (p₁ p₂ : Pos) (mem : (p₁, p₂) ∈ accum.push positions) : Matches.Spec v.1 m.haystack (p₁, p₂) := by
      simp [Array.push_eq_append_singleton] at mem
      cases mem with
      | inl mem => exact inv (p₁, p₂) mem
      | inr eq => exact eq ▸ spec
    exact ih v' inv'
  | case2 m accum next_none? =>
    -- next match is not found
    rw [findAll.go, next_none?]
    dsimp
    exact inv

theorem captures_of_mem_findAll {positions} (mem : positions ∈ re.findAll haystack)
  (s : re.IsSearchRegex) :
  Matches.Spec s haystack positions := by
  simp [Regex.findAll] at mem
  have v := Matches.vaild_matches haystack s
  exact captures_of_mem_findAll.go v (by simp) positions mem

theorem captures_of_capture_some {captured} (h : re.capture haystack = .some captured)
  (s : re.IsSearchRegex) :
  captured.Spec s haystack := by
  simp [Regex.capture] at h
  have ⟨_, h⟩ := h
  have v := Captures.valid_captures haystack s
  exact (Captures.captures_of_next?_some h v).2

theorem captures_of_mem_captureAll.go {captures : Captures} {accum : Array CapturedGroups}
  (v : captures.Valid) (inv : ∀ captured ∈ accum, captured.Spec v.1 captures.haystack) :
  ∀ captured ∈ captureAll.go captures accum, captured.Spec v.1 captures.haystack := by
  induction captures, accum using captureAll.go.induct with
  | case1 captures accum groups captures' next?_some ih =>
    -- next capture is found
    rw [captureAll.go, next?_some]
    simp
    have regex_eq := Captures.regex_eq_of_next?_some next?_some
    have haystack_eq := Captures.haystack_eq_of_next?_some next?_some
    simp [regex_eq, haystack_eq] at ih

    have ⟨v', spec⟩ := Captures.captures_of_next?_some next?_some v
    have inv' (captured : CapturedGroups) (mem : captured ∈ accum.push groups) : captured.Spec v.1 captures.haystack := by
      simp [Array.push_eq_append_singleton] at mem
      cases mem with
      | inl mem => exact inv captured mem
      | inr eq => exact eq ▸ spec
    exact ih v' inv'
  | case2 captures accum next?_none =>
    -- next capture is not found
    rw [captureAll.go, next?_none]
    simp
    exact inv

theorem captures_of_mem_captureAll {captured} (mem : captured ∈ re.captureAll haystack)
  (s : re.IsSearchRegex) :
  captured.Spec s haystack := by
  simp [Regex.captureAll] at mem
  have v := Captures.valid_captures haystack s
  exact captures_of_mem_captureAll.go v (by simp) captured mem

end Regex
