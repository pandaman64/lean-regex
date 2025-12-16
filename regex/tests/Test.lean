import Regex.Regex.Utilities
import Regex.Regex.Captures
import Regex.Regex.Elab
import Regex.Backtracker

open String (Slice Pos Pos)

namespace Regex.Test

def slice (s : String) (startInclusive endExclusive : Nat)
  (isValid₁ : Pos.Raw.IsValid s ⟨startInclusive⟩ := by decide)
  (isValid₂ : Pos.Raw.IsValid s ⟨endExclusive⟩ := by decide)
  (le : startInclusive ≤ endExclusive := by decide) :
  Slice :=
  ⟨s, ⟨⟨startInclusive⟩, isValid₁⟩, ⟨⟨endExclusive⟩, isValid₂⟩, le⟩

def cg {s : String} (ps : Array (Option Nat)) (isValid : ∀ p ∈ ps, (h : p.isSome) → Pos.Raw.IsValid s ⟨p.get h⟩ := by decide) : CapturedGroups s :=
  ⟨ps.attach.map fun ⟨p, mem⟩ => match p with | .some p => .validPos ⟨⟨p⟩, isValid p mem (by grind)⟩ | .none => .sentinel s⟩

deriving instance DecidableEq for Slice

local instance : Repr Slice where
  reprPrec s n := f!"⟨{s.str}, {reprPrec s.startInclusive.offset n}, {reprPrec s.endExclusive.offset n}⟩"

namespace Epsilon

def epsilon := re! r##""##
#guard epsilon.find "" = .some (slice "" 0 0)

def star := re! r##"a*"##
#guard star.find "" = .some (slice "" 0 0)

end Epsilon

namespace Priority

def re := re! r##"bool|boolean"##
#guard re.find "boolean" = .some (slice "boolean" 0 4)

def re' := re! r##"|x"##
#guard re'.find "x" = .some (slice "x" 0 0)

def re'' := re! r##"x|"##
#guard re''.find "x" = .some (slice "x" 0 1)

def empty_110 := re! r##"b|"##
-- Why does only Rust skip (⟨2⟩, ⟨2⟩)? https://regex101.com/r/ZQcPeh/1
-- #guard re'''.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]
#guard empty_110.findAll "abc" = #[slice "abc" 0 0, slice "abc" 1 2, slice "abc" 2 2, slice "abc" 3 3]

def empty_310 := re! r##"b||"##
-- Why does only Rust skip (⟨2⟩, ⟨2⟩)? https://regex101.com/r/j7z8gd/1
-- #guard re'''.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]
#guard empty_110.findAll "abc" = #[slice "abc" 0 0, slice "abc" 1 2, slice "abc" 2 2, slice "abc" 3 3]

def empty_600 := re! r##"(?:|a)*"##
#eval empty_600.findAll "aaa"
-- BUG: we report [⟨"aaa", ⟨0⟩, ⟨3⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]
-- #guard empty_600.findAll "aaa" = #[⟨"aaa", ⟨0⟩, ⟨0⟩⟩, ⟨"aaa", ⟨1⟩, ⟨1⟩⟩, ⟨"aaa", ⟨2⟩, ⟨2⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]

def empty_610 := re! r##"(?:|a)+"##
#eval empty_610.findAll "aaa"
-- BUG: we report [⟨"aaa", ⟨0⟩, ⟨3⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]
-- #guard empty_610.findAll "aaa" = #[⟨"aaa", ⟨0⟩, ⟨0⟩⟩, ⟨"aaa", ⟨1⟩, ⟨1⟩⟩, ⟨"aaa", ⟨2⟩, ⟨2⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]

-- Non-greedy matching tests
def non_greedy_star := re! r##"a*?"##
#guard non_greedy_star.capture "" = .some (cg #[.some 0, .some 0])
#guard non_greedy_star.capture "a" = .some (cg #[.some 0, .some 0])
#guard non_greedy_star.capture "aa" = .some (cg #[.some 0, .some 0])
#guard non_greedy_star.capture "aaa" = .some (cg #[.some 0, .some 0])

def non_greedy_plus := re! r##"a+?"##
#guard non_greedy_plus.capture "" = .none
#guard non_greedy_plus.capture "a" = .some (cg #[.some 0, .some 1])
#guard non_greedy_plus.capture "aa" = .some (cg #[.some 0, .some 1])
#guard non_greedy_plus.capture "aaa" = .some (cg #[.some 0, .some 1])

def non_greedy_quantifier := re! r##"a{2,4}?"##
#guard non_greedy_quantifier.capture "" = .none
#guard non_greedy_quantifier.capture "a" = .none
#guard non_greedy_quantifier.capture "aa" = .some (cg #[.some 0, .some 2])
#guard non_greedy_quantifier.capture "aaa" = .some (cg #[.some 0, .some 2])
#guard non_greedy_quantifier.capture "aaaa" = .some (cg #[.some 0, .some 2])

def non_greedy_word_boundary := re! r##"\b\w+?\b"##
#eval non_greedy_word_boundary.captureAll "hello world"
#eval non_greedy_word_boundary.captureAll "a b c"
#guard non_greedy_word_boundary.captureAll "hello world" = #[
  cg #[.some 0, .some 5],
  cg #[.some 6, .some 11]
]
#guard non_greedy_word_boundary.captureAll "a b c" = #[
  cg #[.some 0, .some 1],
  cg #[.some 2, .some 3],
  cg #[.some 4, .some 5]
]

end Priority

namespace Comparison

private def _root_.Regex.bt (regex : Regex) := { regex with useBacktracker := true }

def simple_char := re! r##"a"##
#guard simple_char.capture "a" = .some (cg #[.some 0, .some 1])
#guard simple_char.capture "b" = .none
#guard simple_char.bt.capture "a" = .some (cg #[.some 0, .some 1])
#guard simple_char.bt.capture "b" = .none

def simple_concat := re! r##"ab"##
#guard simple_concat.capture "ab" = .some (cg #[.some 0, .some 2])
#guard simple_concat.capture "ac" = .none
#guard simple_concat.bt.capture "ab" = .some (cg #[.some 0, .some 2])
#guard simple_concat.bt.capture "ac" = .none

def simple_alt := re! r##"a|b"##
#guard simple_alt.capture "a" = .some (cg #[.some 0, .some 1])
#guard simple_alt.capture "b" = .some (cg #[.some 0, .some 1])
#guard simple_alt.capture "c" = .none
#guard simple_alt.bt.capture "a" = .some (cg #[.some 0, .some 1])
#guard simple_alt.bt.capture "b" = .some (cg #[.some 0, .some 1])
#guard simple_alt.bt.capture "c" = .none

def simple_star := re! r##"a*"##
#guard simple_star.capture "" = .some (cg #[.some 0, .some 0])
#guard simple_star.capture "a" = .some (cg #[.some 0, .some 1])
#guard simple_star.capture "aa" = .some (cg #[.some 0, .some 2])
#guard simple_star.bt.capture "" = .some (cg #[.some 0, .some 0])
#guard simple_star.bt.capture "a" = .some (cg #[.some 0, .some 1])
#guard simple_star.bt.capture "aa" = .some (cg #[.some 0, .some 2])

def complex_pattern := re! r##"(a|b)*c"##
#guard complex_pattern.capture "c" = .some (cg #[.some 0, .some 1, .none, .none])
#guard complex_pattern.capture "ac" = .some (cg #[.some 0, .some 2, .some 0, .some 1])
#guard complex_pattern.capture "bc" = .some (cg #[.some 0, .some 2, .some 0, .some 1])
#guard complex_pattern.capture "xyzaabbczy" = .some (cg #[.some 3, .some 8, .some 6, .some 7])
#guard complex_pattern.capture "d" = .none
#guard complex_pattern.bt.capture "c" = .some (cg #[.some 0, .some 1, .none, .none])
#guard complex_pattern.bt.capture "ac" = .some (cg #[.some 0, .some 2, .some 0, .some 1])
#guard complex_pattern.bt.capture "bc" = .some (cg #[.some 0, .some 2, .some 0, .some 1])
#guard complex_pattern.bt.capture "xyzaabbczy" = .some (cg #[.some 3, .some 8, .some 6, .some 7])
#guard complex_pattern.bt.capture "d" = .none

def nested_groups := re! r##"(a(b(c)))"##
#guard nested_groups.capture "abc" = .some (cg #[.some 0, .some 3, .some 0, .some 3, .some 1, .some 3, .some 2, .some 3])
#guard nested_groups.capture "ab" = .none
#guard nested_groups.capture "a" = .none
#guard nested_groups.bt.capture "abc" = .some (cg #[.some 0, .some 3, .some 0, .some 3, .some 1, .some 3, .some 2, .some 3])
#guard nested_groups.bt.capture "ab" = .none
#guard nested_groups.bt.capture "a" = .none

def complex_quantifiers := re! r##"a{2,4}b{1,3}"##
#guard complex_quantifiers.capture "aab" = .some (cg #[.some 0, .some 3])
#guard complex_quantifiers.capture "aaabbb" = .some (cg #[.some 0, .some 6])
#guard complex_quantifiers.capture "ab" = .none
#guard complex_quantifiers.capture "aabbb" = .some (cg #[.some 0, .some 5])
#guard complex_quantifiers.bt.capture "aab" = .some (cg #[.some 0, .some 3])
#guard complex_quantifiers.bt.capture "aaabbb" = .some (cg #[.some 0, .some 6])
#guard complex_quantifiers.bt.capture "ab" = .none
#guard complex_quantifiers.bt.capture "aabbb" = .some (cg #[.some 0, .some 5])

def alternation_with_groups := re! r##"(ab|cd)(ef|gh)"##
#guard alternation_with_groups.capture "abef" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.capture "cdgh" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.capture "abgh" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.capture "cdef" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.bt.capture "abef" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.bt.capture "cdgh" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.bt.capture "abgh" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])
#guard alternation_with_groups.bt.capture "cdef" = .some (cg #[.some 0, .some 4, .some 0, .some 2, .some 2, .some 4])

def complex_character_classes := re! r##"[a-zA-Z0-9_]+@[a-zA-Z0-9]+\.[a-zA-Z]{2,}"##
#guard complex_character_classes.capture "test@example.com" = .some (cg #[.some 0, .some 16])
#guard complex_character_classes.capture "user123@domain.org" = .some (cg #[.some 0, .some 18])
#guard complex_character_classes.capture "invalid@email" = .none
#guard complex_character_classes.capture "test@.com" = .none
#guard complex_character_classes.bt.capture "test@example.com" = .some (cg #[.some 0, .some 16])
#guard complex_character_classes.bt.capture "user123@domain.org" = .some (cg #[.some 0, .some 18])
#guard complex_character_classes.bt.capture "invalid@email" = .none
#guard complex_character_classes.bt.capture "test@.com" = .none

def nested_quantifiers := re! r##"(a+)*b"##
#guard nested_quantifiers.capture "b" = .some (cg #[.some 0, .some 1, .none, .none])
#guard nested_quantifiers.capture "ab" = .some (cg #[.some 0, .some 2, .some 0, .some 1])
#guard nested_quantifiers.capture "aaab" = .some (cg #[.some 0, .some 4, .some 0, .some 3])
#guard nested_quantifiers.capture "a" = .none
#guard nested_quantifiers.capture "ba" = .some (cg #[.some 0, .some 1, .none, .none])
#guard nested_quantifiers.bt.capture "b" = .some (cg #[.some 0, .some 1, .none, .none])
#guard nested_quantifiers.bt.capture "ab" = .some (cg #[.some 0, .some 2, .some 0, .some 1])
#guard nested_quantifiers.bt.capture "aaab" = .some (cg #[.some 0, .some 4, .some 0, .some 3])
#guard nested_quantifiers.bt.capture "a" = .none
#guard nested_quantifiers.bt.capture "ba" = .some (cg #[.some 0, .some 1, .none, .none])

def alt_in_alt_100 := re! r##"ab?|$"##
#eval alt_in_alt_100.captureAll "az"
#eval alt_in_alt_100.bt.captureAll "az"

def word_class := re! r##"\w+"##
#guard word_class.capture "hello_world" = .some (cg #[.some 0, .some 11])
#guard word_class.capture "test_123" = .some (cg #[.some 0, .some 8])
#guard word_class.capture "special@chars" = .some (cg #[.some 0, .some 7])
#guard word_class.bt.capture "hello_world" = .some (cg #[.some 0, .some 11])
#guard word_class.bt.capture "test_123" = .some (cg #[.some 0, .some 8])
#guard word_class.bt.capture "special@chars" = .some (cg #[.some 0, .some 7])

--
-- word boundary tests
--
def word_boundary_01 := re! r##"\b"##

-- name = "wb1"
#guard word_boundary_01.capture "" = none
#guard word_boundary_01.bt.capture "" = none

-- name = "wb2"
#guard word_boundary_01.captureAll "a" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]
#guard word_boundary_01.bt.captureAll "a" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]

-- name = "wb3"
#guard word_boundary_01.captureAll "ab" = #[
  cg #[.some 0, .some 0],
  cg #[.some 2, .some 2],
  cg #[.some 2, .some 2]
]
#guard word_boundary_01.bt.captureAll "ab" = #[
  cg #[.some 0, .some 0],
  cg #[.some 2, .some 2],
  cg #[.some 2, .some 2]
]

def word_boundary_02 := re! r##"^\b"##

-- name = "wb4"
#guard  word_boundary_02.captureAll "ab" = #[
  cg #[.some 0, .some 0]
]
#guard  word_boundary_02.bt.captureAll "ab" = #[
  cg #[.some 0, .some 0]
]

def word_boundary_03 := re! r##"\b$"##

-- name = "wb5"
#guard word_boundary_03.captureAll "ab" = #[
  cg #[.some 2, .some 2],
  cg #[.some 2, .some 2]
]
#guard word_boundary_03.bt.captureAll "ab" = #[
  cg #[.some 2, .some 2],
  cg #[.some 2, .some 2]
]

def word_boundary_04 := re! r##"^\b$"##

-- name = "wb6"
#guard word_boundary_04.captureAll "ab" = #[]
#guard word_boundary_04.bt.captureAll "ab" = #[]

def word_boundary_05 := re! r##"\bbar\b"##

-- name = "wb7"
#guard word_boundary_05.captureAll "nobar bar foo bar" = #[
  cg #[.some 6, .some 9],
  cg #[.some 14, .some 17]
]
#guard word_boundary_05.bt.captureAll "nobar bar foo bar" = #[
  cg #[.some 6, .some 9],
  cg #[.some 14, .some 17]
]

def word_boundary_06 := re! r##"a\b"##

-- name = "wb8"
#guard word_boundary_06.captureAll "faoa x" = #[
  cg #[.some 3, .some 4]
]
#guard word_boundary_06.bt.captureAll "faoa x" = #[
  cg #[.some 3, .some 4]
]

def word_boundary_07 := re! r##"\bbar"##

-- name = "wb9"
#guard word_boundary_07.captureAll "bar x" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_07.bt.captureAll "bar x" = #[
  cg #[.some 0, .some 3]
]

-- name = "wb10"
#guard word_boundary_07.captureAll "foo\nbar x" = #[
  cg #[.some 4, .some 7]
]
#guard word_boundary_07.bt.captureAll "foo\nbar x" = #[
  cg #[.some 4, .some 7]
]

def word_boundary_08 := re! r##"bar\b"##

-- name = "wb11"
#guard word_boundary_08.captureAll "foobar" = #[
  cg #[.some 3, .some 6]
]
#guard word_boundary_08.bt.captureAll "foobar" = #[
  cg #[.some 3, .some 6]
]

-- name = "wb12"
#guard word_boundary_08.captureAll "foobar\nxxx" = #[
  cg #[.some 3, .some 6]
]
#guard word_boundary_08.bt.captureAll "foobar\nxxx" = #[
  cg #[.some 3, .some 6]
]

def word_boundary_09 := re! r##"(?:foo|bar|[A-Z])\b"##

-- name = "wb13"
#guard word_boundary_09.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_09.bt.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]

-- name = "wb14"
#guard word_boundary_09.captureAll "foo\n" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_09.bt.captureAll "foo\n" = #[
  cg #[.some 0, .some 3]
]

def word_boundary_10 := re! r##"\b(?:foo|bar|[A-Z])"##

-- name = "wb15"
#guard word_boundary_10.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_10.bt.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]

def word_boundary_11 := re! r##"\b(?:foo|bar|[A-Z])\b"##

-- name = "wb16"
#guard word_boundary_11.captureAll "X" = #[
  cg #[.some 0, .some 1]
]
#guard word_boundary_11.bt.captureAll "X" = #[
  cg #[.some 0, .some 1]
]

-- name = "wb17"
#guard word_boundary_11.captureAll "XY" = #[]
#guard word_boundary_11.bt.captureAll "XY" = #[]

-- name = "wb18"
#guard word_boundary_11.captureAll "bar" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_11.bt.captureAll "bar" = #[
  cg #[.some 0, .some 3]
]

-- name = "wb19"
#guard word_boundary_11.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_11.bt.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]

-- name = "wb20"
#guard word_boundary_11.captureAll "foo\n" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_11.bt.captureAll "foo\n" = #[
  cg #[.some 0, .some 3]
]

-- name = "wb21"
#guard word_boundary_11.captureAll "ffoo bbar N x" = #[
  cg #[.some 10, .some 11]
]
#guard word_boundary_11.bt.captureAll "ffoo bbar N x" = #[
  cg #[.some 10, .some 11]
]

def word_boundary_12 := re! r##"\b(?:fo|foo)\b"##

-- name = "wb22"
#guard word_boundary_12.captureAll "fo" = #[
  cg #[.some 0, .some 2]
]
#guard word_boundary_12.bt.captureAll "fo" = #[
  cg #[.some 0, .some 2]
]

-- name = "wb23"
#guard word_boundary_12.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_12.bt.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]

def word_boundary_13 := re! r##"\b\b"##

-- name = "wb24"
#guard word_boundary_13.captureAll "" = #[]
#guard word_boundary_13.bt.captureAll "" = #[]

-- name = "wb25"
#guard word_boundary_13.captureAll "a" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]
#guard word_boundary_13.bt.captureAll "a" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]

def word_boundary_14 := re! r##"\b$"##

-- name = "wb26"
#guard word_boundary_14.captureAll "" = #[]
#guard word_boundary_14.bt.captureAll "" = #[]

-- name = "wb27"
#guard word_boundary_14.captureAll "x" = #[
  cg #[.some 1, .some 1],
  cg #[.some 1, .some 1]
]
#guard word_boundary_14.bt.captureAll "x" = #[
  cg #[.some 1, .some 1],
  cg #[.some 1, .some 1]
]

-- name = "wb28"
#guard word_boundary_14.captureAll "y x" = #[
  cg #[.some 3, .some 3],
  cg #[.some 3, .some 3]
]
#guard word_boundary_14.bt.captureAll "y x" = #[
  cg #[.some 3, .some 3],
  cg #[.some 3, .some 3]
]

def word_boundary_15 := re! r##"(?:\b).$"##

-- name = "wb29"
#guard word_boundary_15.captureAll "x" = #[
  cg #[.some 0, .some 1]
]
#guard word_boundary_15.bt.captureAll "x" = #[
  cg #[.some 0, .some 1]
]

def word_boundary_16 := re! r##"^\b(?:fo|foo)\b"##

-- name = "wb30"
#guard word_boundary_16.captureAll "fo" = #[
  cg #[.some 0, .some 2]
]
#guard word_boundary_16.bt.captureAll "fo" = #[
  cg #[.some 0, .some 2]
]

-- name = "wb31"
#guard word_boundary_16.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]
#guard word_boundary_16.bt.captureAll "foo" = #[
  cg #[.some 0, .some 3]
]

def word_boundary_17 := re! r##"^\b$"##

-- name = "wb32"
#guard word_boundary_17.captureAll "" = #[]
#guard word_boundary_17.bt.captureAll "" = #[]

-- name = "wb33"
#guard word_boundary_17.captureAll "x" = #[]
#guard word_boundary_17.bt.captureAll "x" = #[]

def word_boundary_18 := re! r##"^(?:\b).$"##

-- name = "wb34"
#guard word_boundary_18.captureAll "x" = #[
  cg #[.some 0, .some 1]
]
#guard word_boundary_18.bt.captureAll "x" = #[
  cg #[.some 0, .some 1]
]

def word_boundary_19 := re! r##"^(?:\b).(?:\b)$"##

-- name = "wb35"
#guard word_boundary_19.captureAll "x" = #[
  cg #[.some 0, .some 1],
]
#guard word_boundary_19.bt.captureAll "x" = #[
  cg #[.some 0, .some 1]
]

def word_boundary_20 := re! r##"^^^^^\b$$$$$"##

-- name = "wb36"
#guard word_boundary_20.captureAll "" = #[]
#guard word_boundary_20.bt.captureAll "" = #[]

def word_boundary_21 := re! r##"^^^^^(?:\b).$$$$$"##

-- name = "wb37"
#guard word_boundary_21.captureAll "x" = #[
  cg #[.some 0, .some 1]
]
#guard word_boundary_21.bt.captureAll "x" = #[
  cg #[.some 0, .some 1]
]

def word_boundary_22 := re! r##"^^^^^\b$$$$$"##

-- name = "wb38"
#guard word_boundary_22.captureAll "x" = #[]
#guard word_boundary_22.bt.captureAll "x" = #[]

def word_boundary_23 := re! r##"^^^^^(?:\b\b\b).(?:\b\b\b)$$$$$"##

-- name = "wb39"
#guard word_boundary_23.captureAll "x" = #[
  cg #[.some 0, .some 1]
]
#guard word_boundary_23.bt.captureAll "x" = #[
  cg #[.some 0, .some 1]
]

def word_boundary_24 := re! r##"(?:\b).+(?:\b)"##

-- name = "wb40"
#guard word_boundary_24.captureAll "$$abc$$" = #[
  cg #[.some 2, .some 5]
]
#guard word_boundary_24.bt.captureAll "$$abc$$" = #[
  cg #[.some 2, .some 5]
]

def word_boundary_25 := re! r##"\b"##

-- name = "wb41"
#guard word_boundary_25.captureAll "a b c" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1],
  cg #[.some 2, .some 2],
  cg #[.some 3, .some 3],
  cg #[.some 4, .some 4],
  cg #[.some 5, .some 5]
]
#guard word_boundary_25.bt.captureAll "a b c" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1],
  cg #[.some 2, .some 2],
  cg #[.some 3, .some 3],
  cg #[.some 4, .some 4],
  cg #[.some 5, .some 5]
]

def word_boundary_26 := re! r##"\bfoo\b"##

-- name = "wb42"
#guard word_boundary_26.captureAll "zzz foo zzz" = #[
  cg #[.some 4, .some 7]
]
#guard word_boundary_26.bt.captureAll "zzz foo zzz" = #[
  cg #[.some 4, .some 7]
]

def word_boundary_27 := re! r##"\b^"##

-- name = "wb43"
#guard word_boundary_27.captureAll "ab" = #[
  cg #[.some 0, .some 0]
]
#guard word_boundary_27.bt.captureAll "ab" = #[
  cg #[.some 0, .some 0]
]

-- Non word boundary tests

def non_word_boundary_01 := re! r##"\Bfoo\B"##

-- name = "nb1"
#guard non_word_boundary_01.captureAll "n foo xfoox that" = #[
  cg #[.some 7, .some 10]
]
#guard non_word_boundary_01.bt.captureAll "n foo xfoox that" = #[
  cg #[.some 7, .some 10]
]

def non_word_boundary_02 := re! r##"a\B"##

-- name = "nb2"
#guard non_word_boundary_02.captureAll "faoa x" = #[
  cg #[.some 1, .some 2]
]
#guard non_word_boundary_02.bt.captureAll "faoa x" = #[
  cg #[.some 1, .some 2]
]

def non_word_boundary_03 := re! r##"\Bbar"##

-- name = "nb3"
#guard non_word_boundary_03.captureAll "bar x" = #[]
#guard non_word_boundary_03.bt.captureAll "bar x" = #[]

-- name = "nb4"
#guard non_word_boundary_03.captureAll "foo\nbar x" = #[]
#guard non_word_boundary_03.bt.captureAll "foo\nbar x" = #[]

def non_word_boundary_04 := re! r##"bar\B"##

-- name = "nb5"
#guard non_word_boundary_04.captureAll "foobar" = #[]
#guard non_word_boundary_04.bt.captureAll "foobar" = #[]

-- name = "nb6"
#guard non_word_boundary_04.captureAll "foobar\nxxx" = #[]
#guard non_word_boundary_04.bt.captureAll "foobar\nxxx" = #[]

def non_word_boundary_05 := re! r##"(?:foo|bar|[A-Z])\B"##

-- name = "nb7"
#guard non_word_boundary_05.captureAll "foox" = #[
  cg #[.some 0, .some 3]
]
#guard non_word_boundary_05.bt.captureAll "foox" = #[
  cg #[.some 0, .some 3]
]

def non_word_boundary_06 := re! r##"(?:foo|bar|[A-Z])\B"##

-- name = "nb8"
#guard non_word_boundary_06.captureAll "foo\n" = #[]
#guard non_word_boundary_06.bt.captureAll "foo\n" = #[]

def non_word_boundary_07 := re! r##"\B"##

-- name = "nb9"
#guard non_word_boundary_07.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_07.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

def non_word_boundary_08 := re! r##"\B"##

-- name = "nb10"
#guard non_word_boundary_08.captureAll "x" = #[]
#guard non_word_boundary_08.bt.captureAll "x" = #[]

def non_word_boundary_09 := re! r##"\B(?:foo|bar|[A-Z])"##

-- name = "nb11"
#guard non_word_boundary_09.captureAll "foo" = #[]
#guard non_word_boundary_09.bt.captureAll "foo" = #[]

def non_word_boundary_10 := re! r##"\B(?:foo|bar|[A-Z])\B"##

-- name = "nb12"
#guard non_word_boundary_10.captureAll "xXy" = #[
  cg #[.some 1, .some 2]
]
#guard non_word_boundary_10.bt.captureAll "xXy" = #[
  cg #[.some 1, .some 2]
]

-- name = "nb13"
#guard non_word_boundary_10.captureAll "XY" = #[]
#guard non_word_boundary_10.bt.captureAll "XY" = #[]

-- name = "nb14"
#guard non_word_boundary_10.captureAll "XYZ" = #[
  cg #[.some 1, .some 2]
]
#guard non_word_boundary_10.bt.captureAll "XYZ" = #[
  cg #[.some 1, .some 2]
]

-- name = "nb15"
#guard non_word_boundary_10.captureAll "abara" = #[
  cg #[.some 1, .some 4]
]
#guard non_word_boundary_10.bt.captureAll "abara" = #[
  cg #[.some 1, .some 4]
]

-- name = "nb16"
#guard non_word_boundary_10.captureAll "xfoo_" = #[
  cg #[.some 1, .some 4]
]
#guard non_word_boundary_10.bt.captureAll "xfoo_" = #[
  cg #[.some 1, .some 4]
]

-- name = "nb17"
#guard non_word_boundary_10.captureAll "xfoo\n" = #[]
#guard non_word_boundary_10.bt.captureAll "xfoo\n" = #[]

-- name = "nb18"
#guard non_word_boundary_10.captureAll "foo bar vNX" = #[
  cg #[.some 9, .some 10]
]
#guard non_word_boundary_10.bt.captureAll "foo bar vNX" = #[
  cg #[.some 9, .some 10]
]

def non_word_boundary_11 := re! r##"\B(?:foo|fo)\B"##

-- name = "nb19"
#guard non_word_boundary_11.captureAll "xfoo" = #[
  cg #[.some 1, .some 3]
]
#guard non_word_boundary_11.bt.captureAll "xfoo" = #[
  cg #[.some 1, .some 3]
]

def non_word_boundary_12 := re! r##"\B(?:foo|fo)\B"##

-- name = "nb20"
#guard non_word_boundary_12.captureAll "xfooo" = #[
  cg #[.some 1, .some 4]
]
#guard non_word_boundary_12.bt.captureAll "xfooo" = #[
  cg #[.some 1, .some 4]
]

def non_word_boundary_13 := re! r##"\B\B"##

-- name = "nb21"
#guard non_word_boundary_13.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_13.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

-- name = "nb22"
#guard non_word_boundary_13.captureAll "x" = #[]
#guard non_word_boundary_13.bt.captureAll "x" = #[]

def non_word_boundary_14 := re! r##"\B$"##

-- name = "nb23"
#guard non_word_boundary_14.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_14.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

-- name = "nb24"
#guard non_word_boundary_14.captureAll "x" = #[]
#guard non_word_boundary_14.bt.captureAll "x" = #[]

-- name = "nb25"
#guard non_word_boundary_14.captureAll "y x" = #[]
#guard non_word_boundary_14.bt.captureAll "y x" = #[]

def non_word_boundary_15 := re! r##"\B.$"##

-- name = "nb26"
#guard non_word_boundary_15.captureAll "x" = #[]
#guard non_word_boundary_15.bt.captureAll "x" = #[]

def non_word_boundary_16 := re! r##"^\B(?:fo|foo)\B"##

-- name = "nb27"
#guard non_word_boundary_16.captureAll "fo" = #[]
#guard non_word_boundary_16.bt.captureAll "fo" = #[]

-- name = "nb28"
#guard non_word_boundary_16.captureAll "foo" = #[]
#guard non_word_boundary_16.bt.captureAll "foo" = #[]

def non_word_boundary_17 := re! r##"^\B"##

-- name = "nb29"
#guard non_word_boundary_17.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_17.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

-- name = "nb30"
#guard non_word_boundary_17.captureAll "x" = #[]
#guard non_word_boundary_17.bt.captureAll "x" = #[]

def non_word_boundary_18 := re! r##"^\B\B"##

-- name = "nb31"
#guard non_word_boundary_18.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_18.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

-- name = "nb32"
#guard non_word_boundary_18.captureAll "x" = #[]
#guard non_word_boundary_18.bt.captureAll "x" = #[]

def non_word_boundary_19 := re! r##"^\B$"##

-- name = "nb33"
#guard non_word_boundary_19.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_19.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

-- name = "nb34"
#guard non_word_boundary_19.captureAll "x" = #[]
#guard non_word_boundary_19.bt.captureAll "x" = #[]

def non_word_boundary_20 := re! r##"^\B.$"##

-- name = "nb35"
#guard non_word_boundary_20.captureAll "x" = #[]
#guard non_word_boundary_20.bt.captureAll "x" = #[]

def non_word_boundary_21 := re! r##"^\B.\B$"##

-- name = "nb36"
#guard non_word_boundary_21.captureAll "x" = #[]
#guard non_word_boundary_21.bt.captureAll "x" = #[]

def non_word_boundary_22 := re! r##"^^^^^\B$$$$$"##

-- name = "nb37"
#guard non_word_boundary_22.captureAll "" = #[
  cg #[.some 0, .some 0]
]
#guard non_word_boundary_22.bt.captureAll "" = #[
  cg #[.some 0, .some 0]
]

def non_word_boundary_23 := re! r##"^^^^^\B.$$$$$"##

-- name = "nb38"
#guard non_word_boundary_23.captureAll "x" = #[]
#guard non_word_boundary_23.bt.captureAll "x" = #[]

def non_word_boundary_24 := re! r##"^^^^^\B$$$$$"##

-- name = "nb39"
#guard non_word_boundary_24.captureAll "x" = #[]
#guard non_word_boundary_24.bt.captureAll "x" = #[]

-- unicode tests
-- unicode1* and unicode2* work for both Unicode and ASCII because all matches
-- are reported as byte offsets, and « and » do not correspond to word
-- boundaries at either the character or byte level.

--
-- Unicode word boundary tests
--
def unicode_word_boundary_01 := re! r##"\bx\b"##

-- name = "unicode1"
#guard unicode_word_boundary_01.captureAll "«x" = #[
  cg #[.some 2, .some 3]
]
#guard unicode_word_boundary_01.bt.captureAll "«x" = #[
  cg #[.some 2, .some 3]
]

-- name = "unicode1-only-ascii"
#guard unicode_word_boundary_01.captureAll "«x" = #[
  cg #[.some 2, .some 3]
]
#guard unicode_word_boundary_01.bt.captureAll "«x" = #[
  cg #[.some 2, .some 3]
]

-- name = "unicode2"
#guard unicode_word_boundary_01.captureAll "x»" = #[
  cg #[.some 0, .some 1]
]
#guard unicode_word_boundary_01.bt.captureAll "x»" = #[
  cg #[.some 0, .some 1]
]

-- name = "unicode2-only-ascii"
#guard unicode_word_boundary_01.captureAll "x»" = #[
  cg #[.some 0, .some 1]
]
#guard unicode_word_boundary_01.bt.captureAll "x»" = #[
  cg #[.some 0, .some 1]
]

-- FIXME: This test is not working as expected because
-- we only check for ASCII alphanumeric characters.
-- name = "unicode3"
-- #eval unicode_word_boundary_01.captureAll "áxβ"
-- #guard unicode_word_boundary_01.captureAll "áxβ" = #[]
-- #guard unicode_word_boundary_01.bt.captureAll "áxβ" = #[]

-- name = "unicode3-only-ascii"
#guard unicode_word_boundary_01.captureAll "áxβ" = #[
  cg #[.some 2, .some 3]
]
#guard unicode_word_boundary_01.bt.captureAll "áxβ" = #[
  cg #[.some 2, .some 3]
]

def unicode_non_word_boundary_01 := re! r##"\Bx\B"##

-- FIXME: This test is not working as expected.
-- name = "unicode4"
-- #eval unicode_word_boundary_02.captureAll "áxβ"
-- #guard unicode_word_boundary_02.captureAll "áxβ" = #[
--  cg #[.some 2, .some 3]
-- ]
-- #guard unicode_word_boundary_02.bt.captureAll "áxβ" = #[
--  cg #[.some 2, .some 3]
-- ]

-- name = "unicode4-only-ascii"
#guard unicode_non_word_boundary_01.captureAll "áxβ" = #[]
#guard unicode_non_word_boundary_01.bt.captureAll "áxβ" = #[]

-- The same as above, but with \b instead of \B as a sanity check.
def unicode_word_boundary_02 := re! r##"\b"##

-- name = "unicode5"
#guard unicode_word_boundary_02.captureAll "0\uFFFF" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]
#guard unicode_word_boundary_02.bt.captureAll "0\uFFFF" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]

-- name = "unicode5-noutf8"
#guard unicode_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]
#guard unicode_word_boundary_02.bt.captureAll "0\xFF\xFF\xFF\xFF" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]

-- name = "unicode5-noutf8-only-ascii"
#guard unicode_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]
#guard unicode_word_boundary_02.bt.captureAll "0\xFF\xFF\xFF\xFF" = #[
  cg #[.some 0, .some 0],
  cg #[.some 1, .some 1]
]

-- Some tests of no particular significance.
def unicode_word_boundary_03 := re! r##"\b[0-9]+\b"##

-- name = "unicode6"
#guard unicode_word_boundary_03.captureAll "foo 123 bar 456 quux 789" = #[
  cg #[.some 4, .some 7],
  cg #[.some 12, .some 15],
  cg #[.some 21, .some 24]
]
#guard unicode_word_boundary_03.bt.captureAll "foo 123 bar 456 quux 789" = #[
  cg #[.some 4, .some 7],
  cg #[.some 12, .some 15],
  cg #[.some 21, .some 24]
]

-- name = "unicode7"
#guard unicode_word_boundary_03.captureAll "foo 123 bar a456 quux 789" = #[
  cg #[.some 4, .some 7],
  cg #[.some 22, .some 25]
]
#guard unicode_word_boundary_03.bt.captureAll "foo 123 bar a456 quux 789" = #[
  cg #[.some 4, .some 7],
  cg #[.some 22, .some 25]
]

-- name = "unicode8"
#guard unicode_word_boundary_03.captureAll "foo 123 bar 456a quux 789" = #[
  cg #[.some 4, .some 7],
  cg #[.some 22, .some 25]
]
#guard unicode_word_boundary_03.bt.captureAll "foo 123 bar 456a quux 789" = #[
  cg #[.some 4, .some 7],
  cg #[.some 22, .some 25]
]

-- A variant of the problem described here:
-- https://github.com/google/re2/blob/89567f5de5b23bb5ad0c26cbafc10bdc7389d1fa/re2/dfa.cc#L658-L667

def unicode_word_boundary_04 := re! r##"(?:\b|%)+"##

-- FIXME: This test is not working as expected.
-- -- name = "alt-with-assertion-repetition"
-- #eval unicode_word_boundary_04.captureAll "z%"
-- #guard unicode_word_boundary_04.captureAll "z%" = #[
--   ⟨"z%", #[.some ⟨1⟩, .some ⟨1⟩]⟩
-- ]
-- #guard unicode_word_boundary_04.bt.captureAll "z%" = #[
--   ⟨"z%", #[.some ⟨1⟩, .some ⟨1⟩]⟩
-- ]

end Comparison

namespace BasicUtilityMethods

def empty := re! ""
#guard empty.test "" = true
#guard empty.test "a" = true
#guard empty.test "aa" = true
#guard empty.test "🐙" = true
#guard empty.count "" = 1
#guard empty.count "a" = 2
#guard empty.count "aa" = 3
#guard empty.count "🐙" = 2
#guard empty.extract "" = .some ""
#guard empty.extract "a" = .some ""
#guard empty.extract "aa" = .some ""
#guard empty.extract "🐙" = .some ""
#guard empty.extractAll "" = #[""]
#guard empty.extractAll "a" = #["", ""]
#guard empty.extractAll "aa" = #["", "", ""]
#guard empty.extractAll "🐙" = #["", ""]

def singleton := re! "a"
#guard singleton.test "" = false
#guard singleton.test "a" = true
#guard singleton.test "🐙" = false
#guard singleton.count "" = 0
#guard singleton.count "a" = 1
#guard singleton.count "🐙" = 0
#guard singleton.extract "" = .none
#guard singleton.extract "a" = .some "a"
#guard singleton.extract "🐙" = .none
#guard singleton.extractAll "" = #[]
#guard singleton.extractAll "a" = #["a"]
#guard singleton.extractAll "🐙" = #[]

def unicode := re! "🐙"
#guard unicode.test "" = false
#guard unicode.test "a" = false
#guard unicode.test "🐙" = true
#guard unicode.count "" = 0
#guard unicode.count "a" = 0
#guard unicode.count "🐙" = 1
#guard unicode.extract "" = .none
#guard unicode.extract "a" = .none
#guard unicode.extract "🐙" = .some "🐙"
#guard unicode.extractAll "" = #[]
#guard unicode.extractAll "a" = #[]
#guard unicode.extractAll "🐙" = #["🐙"]

def date := re! r"\d{4}-\d{2}-\d{2}"
#guard date.test "" = false
#guard date.test "a" = false
#guard date.test "🐙" = false
#guard date.test "2025-05-24-2025-05-26" = true
#guard date.count "" = 0
#guard date.count "a" = 0
#guard date.count "🐙" = 0
#guard date.count "2025-05-24-2025-05-26" = 2
#guard date.extract "" = .none
#guard date.extract "a" = .none
#guard date.extract "🐙" = .none
#guard date.extract "2025-05-24-2025-05-26" = .some "2025-05-24"
#guard date.extractAll "" = #[]
#guard date.extractAll "a" = #[]
#guard date.extractAll "🐙" = #[]
#guard date.extractAll "2025-05-24-2025-05-26" = #["2025-05-24", "2025-05-26"]

def octopuses := re! "(🐙|octopus)+"
#guard octopuses.test "" = false
#guard octopuses.test "a" = false
#guard octopuses.test "🐙" = true
#guard octopuses.test "octopus 🐙 🐙octopus" = true
#guard octopuses.count "" = 0
#guard octopuses.count "a" = 0
#guard octopuses.count "🐙" = 1
#guard octopuses.count "octopus 🐙 🐙octopus" = 3
#guard octopuses.extract "" = .none
#guard octopuses.extract "a" = .none
#guard octopuses.extract "🐙" = .some "🐙"
#guard octopuses.extract "octopus 🐙 🐙octopus" = .some "octopus"
#guard octopuses.extractAll "" = #[]
#guard octopuses.extractAll "a" = #[]
#guard octopuses.extractAll "🐙" = #["🐙"]
#guard octopuses.extractAll "octopus 🐙 🐙octopus" = #["octopus", "🐙", "🐙octopus"]

end BasicUtilityMethods

private def _root_.Regex.splitTest (regex : Regex) (haystack : String) : Array String :=
  regex.split haystack |>.map Slice.copy

namespace Split

-- The tests below check for feature parity with the Rust Regex crate.
#guard (re! "[ \t]+").splitTest "a b \t  c\td    e" = #["a", "b", "c", "d", "e"]
#guard (re! " ").splitTest "Mary had a little lamb" = #["Mary", "had", "a", "little", "lamb"]
#guard (re! "X").splitTest "" = #[""]
#guard (re! "X").splitTest "lionXXtigerXleopard" = #["lion", "", "tiger", "leopard"]
#guard (re! "::").splitTest "lion::tiger::leopard" = #["lion", "tiger", "leopard"]
#guard (re! "X").splitTest "XXXXaXXbXc" = #["", "", "", "", "a", "", "b", "c"]
#guard (re! "/").splitTest "(///)" = #["(", "", "", ")"]
#guard (re! "0").splitTest "010" = #["", "1", ""]
#guard (re! "").splitTest "rust" = #["", "r", "u", "s", "t", ""]
#guard (re! "").splitTest "☃" = #["", "☃", ""]
#guard (re! " ").splitTest "    a  b c" = #["", "", "", "", "a", "", "b", "c"]
#guard (re! " +").splitTest "    a  b c" = #["", "a", "b", "c"]

end Split

namespace Transform

open Regex

def parenthesesRegex := re! r"\((\d+)\)"

def parenthesesToBraces {haystack : String} (captures : CapturedGroups haystack) : String :=
  let digits := captures.get 1 |>.map Slice.copy |>.getD ""
  "{" ++ digits ++ "}"

#guard parenthesesRegex.transform "" parenthesesToBraces = ""
#guard parenthesesRegex.transformAll "" parenthesesToBraces = ""
#guard parenthesesRegex.transform "(123) and ((4))" parenthesesToBraces = "{123} and ((4))"
#guard parenthesesRegex.transformAll "(123) and ((4))" parenthesesToBraces = "{123} and ({4})"

def countRegex := re! r"(a+)(b*)|(c+)"

def countString (name : String) (input : Option Slice) : String :=
  input.map Slice.copy
    |>.map (fun s => toString s.length ++ name)
    |>.getD ""

def countTransform {haystack : String} (captures : CapturedGroups haystack) : String :=
  let as := captures.get 1 |> countString "a"
  let bs := captures.get 2 |> countString "b"
  let cs := captures.get 3 |> countString "c"
  as ++ bs ++ cs

#guard countRegex.transform "a aa aab c cc" countTransform = "1a0b aa aab c cc"
#guard countRegex.transformAll "a aa aab c cc" countTransform = "1a0b 2a0b 2a1b 1c 2c"

end Transform

namespace Regressions

-- Expanded capture groups should have the same tags and thus only the last match should be reported.
def issue_84 := re! "(a){2}"
#guard issue_84.capture "aa" = .some (cg #[.some 0, .some 2, .some 1, .some 2])

end Regressions

end Regex.Test
