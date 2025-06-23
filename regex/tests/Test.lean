import Regex.Regex.Utilities
import Regex.Regex.Elab
import Regex.Backtracker

namespace Epsilon

deriving instance DecidableEq for Substring

def epsilon := Regex.parse! r##""##
#guard epsilon.find "" = .some ⟨"", ⟨0⟩, ⟨0⟩⟩

def star := Regex.parse! r##"a*"##
#guard star.find "" = .some ⟨"", ⟨0⟩, ⟨0⟩⟩

end Epsilon

namespace Priority

def re := Regex.parse! r##"bool|boolean"##
#guard re.find "boolean" = .some ⟨"boolean", ⟨0⟩, ⟨4⟩⟩

def re' := Regex.parse! r##"|x"##
#guard re'.find "x" = .some ⟨"x", ⟨0⟩, ⟨0⟩⟩

def re'' := Regex.parse! r##"x|"##
#guard re''.find "x" = .some ⟨"x", ⟨0⟩, ⟨1⟩⟩

def empty_110 := Regex.parse! r##"b|"##
-- Why does only Rust skip (⟨2⟩, ⟨2⟩)? https://regex101.com/r/ZQcPeh/1
-- #guard re'''.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]
#guard empty_110.findAll "abc" = #[⟨"abc", ⟨0⟩, ⟨0⟩⟩, ⟨"abc", ⟨1⟩, ⟨2⟩⟩, ⟨"abc", ⟨2⟩, ⟨2⟩⟩, ⟨"abc", ⟨3⟩, ⟨3⟩⟩]

def empty_310 := Regex.parse! r##"b||"##
-- Why does only Rust skip (⟨2⟩, ⟨2⟩)? https://regex101.com/r/j7z8gd/1
-- #guard re'''.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]
#guard empty_110.findAll "abc" = #[⟨"abc", ⟨0⟩, ⟨0⟩⟩, ⟨"abc", ⟨1⟩, ⟨2⟩⟩, ⟨"abc", ⟨2⟩, ⟨2⟩⟩, ⟨"abc", ⟨3⟩, ⟨3⟩⟩]

def empty_600 := Regex.parse! r##"(?:|a)*"##
#eval empty_600.findAll "aaa"
-- BUG: we report [⟨"aaa", ⟨0⟩, ⟨3⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]
-- #guard empty_600.findAll "aaa" = #[⟨"aaa", ⟨0⟩, ⟨0⟩⟩, ⟨"aaa", ⟨1⟩, ⟨1⟩⟩, ⟨"aaa", ⟨2⟩, ⟨2⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]

def empty_610 := Regex.parse! r##"(?:|a)+"##
#eval empty_610.findAll "aaa"
-- BUG: we report [⟨"aaa", ⟨0⟩, ⟨3⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]
-- #guard empty_610.findAll "aaa" = #[⟨"aaa", ⟨0⟩, ⟨0⟩⟩, ⟨"aaa", ⟨1⟩, ⟨1⟩⟩, ⟨"aaa", ⟨2⟩, ⟨2⟩⟩, ⟨"aaa", ⟨3⟩, ⟨3⟩⟩]

end Priority

namespace Comparison

private def _root_.Regex.bt (regex : Regex) := { regex with useBacktracker := true }

def simple_char := Regex.parse! r##"a"##
#guard simple_char.capture "a" = .some ⟨"a", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_char.capture "b" = .none
#guard simple_char.bt.capture "a" = .some ⟨"a", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_char.bt.capture "b" = .none

def simple_concat := Regex.parse! r##"ab"##
#guard simple_concat.capture "ab" = .some ⟨"ab", #[.some ⟨0⟩, .some ⟨2⟩]⟩
#guard simple_concat.capture "ac" = .none
#guard simple_concat.bt.capture "ab" = .some ⟨"ab", #[.some ⟨0⟩, .some ⟨2⟩]⟩
#guard simple_concat.bt.capture "ac" = .none

def simple_alt := Regex.parse! r##"a|b"##
#guard simple_alt.capture "a" = .some ⟨"a", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_alt.capture "b" = .some ⟨"b", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_alt.capture "c" = .none
#guard simple_alt.bt.capture "a" = .some ⟨"a", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_alt.bt.capture "b" = .some ⟨"b", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_alt.bt.capture "c" = .none

def simple_star := Regex.parse! r##"a*"##
#guard simple_star.capture "" = .some ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
#guard simple_star.capture "a" = .some ⟨"a", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_star.capture "aa" = .some ⟨"aa", #[.some ⟨0⟩, .some ⟨2⟩]⟩
#guard simple_star.bt.capture "" = .some ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
#guard simple_star.bt.capture "a" = .some ⟨"a", #[.some ⟨0⟩, .some ⟨1⟩]⟩
#guard simple_star.bt.capture "aa" = .some ⟨"aa", #[.some ⟨0⟩, .some ⟨2⟩]⟩

def complex_pattern := Regex.parse! r##"(a|b)*c"##
#guard complex_pattern.capture "c" = .some ⟨"c", #[.some ⟨0⟩, .some ⟨1⟩, .none, .none]⟩
#guard complex_pattern.capture "ac" = .some ⟨"ac", #[.some ⟨0⟩, .some ⟨2⟩, .some ⟨0⟩, .some ⟨1⟩]⟩
#guard complex_pattern.capture "bc" = .some ⟨"bc", #[.some ⟨0⟩, .some ⟨2⟩, .some ⟨0⟩, .some ⟨1⟩]⟩
#guard complex_pattern.capture "xyzaabbczy" = .some ⟨"xyzaabbczy", #[.some ⟨3⟩, .some ⟨8⟩, .some ⟨6⟩, .some ⟨7⟩]⟩
#guard complex_pattern.capture "d" = .none
#guard complex_pattern.bt.capture "c" = .some ⟨"c", #[.some ⟨0⟩, .some ⟨1⟩, .none, .none]⟩
#guard complex_pattern.bt.capture "ac" = .some ⟨"ac", #[.some ⟨0⟩, .some ⟨2⟩, .some ⟨0⟩, .some ⟨1⟩]⟩
#guard complex_pattern.bt.capture "bc" = .some ⟨"bc", #[.some ⟨0⟩, .some ⟨2⟩, .some ⟨0⟩, .some ⟨1⟩]⟩
#guard complex_pattern.bt.capture "xyzaabbczy" = .some ⟨"xyzaabbczy", #[.some ⟨3⟩, .some ⟨8⟩, .some ⟨6⟩, .some ⟨7⟩]⟩
#guard complex_pattern.bt.capture "d" = .none

def nested_groups := Regex.parse! r##"(a(b(c)))"##
#guard nested_groups.capture "abc" = .some ⟨"abc", #[.some ⟨0⟩, .some ⟨3⟩, .some ⟨0⟩, .some ⟨3⟩, .some ⟨1⟩, .some ⟨3⟩, .some ⟨2⟩, .some ⟨3⟩]⟩
#guard nested_groups.capture "ab" = .none
#guard nested_groups.capture "a" = .none
#guard nested_groups.bt.capture "abc" = .some ⟨"abc", #[.some ⟨0⟩, .some ⟨3⟩, .some ⟨0⟩, .some ⟨3⟩, .some ⟨1⟩, .some ⟨3⟩, .some ⟨2⟩, .some ⟨3⟩]⟩
#guard nested_groups.bt.capture "ab" = .none
#guard nested_groups.bt.capture "a" = .none

def complex_quantifiers := Regex.parse! r##"a{2,4}b{1,3}"##
#guard complex_quantifiers.capture "aab" = .some ⟨"aab", #[.some ⟨0⟩, .some ⟨3⟩]⟩
#guard complex_quantifiers.capture "aaabbb" = .some ⟨"aaabbb", #[.some ⟨0⟩, .some ⟨6⟩]⟩
#guard complex_quantifiers.capture "ab" = .none
#guard complex_quantifiers.capture "aabbb" = .some ⟨"aabbb", #[.some ⟨0⟩, .some ⟨5⟩]⟩
#guard complex_quantifiers.bt.capture "aab" = .some ⟨"aab", #[.some ⟨0⟩, .some ⟨3⟩]⟩
#guard complex_quantifiers.bt.capture "aaabbb" = .some ⟨"aaabbb", #[.some ⟨0⟩, .some ⟨6⟩]⟩
#guard complex_quantifiers.bt.capture "ab" = .none
#guard complex_quantifiers.bt.capture "aabbb" = .some ⟨"aabbb", #[.some ⟨0⟩, .some ⟨5⟩]⟩

def alternation_with_groups := Regex.parse! r##"(ab|cd)(ef|gh)"##
#guard alternation_with_groups.capture "abef" = .some ⟨"abef", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.capture "cdgh" = .some ⟨"cdgh", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.capture "abgh" = .some ⟨"abgh", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.capture "cdef" = .some ⟨"cdef", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.bt.capture "abef" = .some ⟨"abef", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.bt.capture "cdgh" = .some ⟨"cdgh", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.bt.capture "abgh" = .some ⟨"abgh", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩
#guard alternation_with_groups.bt.capture "cdef" = .some ⟨"cdef", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨2⟩, .some ⟨2⟩, .some ⟨4⟩]⟩

def complex_character_classes := Regex.parse! r##"[a-zA-Z0-9_]+@[a-zA-Z0-9]+\.[a-zA-Z]{2,}"##
#guard complex_character_classes.capture "test@example.com" = .some ⟨"test@example.com", #[.some ⟨0⟩, .some ⟨16⟩]⟩
#guard complex_character_classes.capture "user123@domain.org" = .some ⟨"user123@domain.org", #[.some ⟨0⟩, .some ⟨18⟩]⟩
#guard complex_character_classes.capture "invalid@email" = .none
#guard complex_character_classes.capture "test@.com" = .none
#guard complex_character_classes.bt.capture "test@example.com" = .some ⟨"test@example.com", #[.some ⟨0⟩, .some ⟨16⟩]⟩
#guard complex_character_classes.bt.capture "user123@domain.org" = .some ⟨"user123@domain.org", #[.some ⟨0⟩, .some ⟨18⟩]⟩
#guard complex_character_classes.bt.capture "invalid@email" = .none
#guard complex_character_classes.bt.capture "test@.com" = .none

def nested_quantifiers := Regex.parse! r##"(a+)*b"##
#guard nested_quantifiers.capture "b" = .some ⟨"b", #[.some ⟨0⟩, .some ⟨1⟩, .none, .none]⟩
#guard nested_quantifiers.capture "ab" = .some ⟨"ab", #[.some ⟨0⟩, .some ⟨2⟩, .some ⟨0⟩, .some ⟨1⟩]⟩
#guard nested_quantifiers.capture "aaab" = .some ⟨"aaab", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨3⟩]⟩
#guard nested_quantifiers.capture "a" = .none
#guard nested_quantifiers.capture "ba" = .some ⟨"ba", #[.some ⟨0⟩, .some ⟨1⟩, .none, .none]⟩
#guard nested_quantifiers.bt.capture "b" = .some ⟨"b", #[.some ⟨0⟩, .some ⟨1⟩, .none, .none]⟩
#guard nested_quantifiers.bt.capture "ab" = .some ⟨"ab", #[.some ⟨0⟩, .some ⟨2⟩, .some ⟨0⟩, .some ⟨1⟩]⟩
#guard nested_quantifiers.bt.capture "aaab" = .some ⟨"aaab", #[.some ⟨0⟩, .some ⟨4⟩, .some ⟨0⟩, .some ⟨3⟩]⟩
#guard nested_quantifiers.bt.capture "a" = .none
#guard nested_quantifiers.bt.capture "ba" = .some ⟨"ba", #[.some ⟨0⟩, .some ⟨1⟩, .none, .none]⟩

def alt_in_alt_100 := re! r##"ab?|$"##
#eval alt_in_alt_100.captureAll "az"
#eval alt_in_alt_100.bt.captureAll "az"

def word_class := Regex.parse! r##"\w+"##
#guard word_class.capture "hello_world" = .some ⟨"hello_world", #[.some ⟨0⟩, .some ⟨11⟩]⟩
#guard word_class.capture "test_123" = .some ⟨"test_123", #[.some ⟨0⟩, .some ⟨8⟩]⟩
#guard word_class.capture "special@chars" = .some ⟨"special@chars", #[.some ⟨0⟩, .some ⟨7⟩]⟩
#guard word_class.bt.capture "hello_world" = .some ⟨"hello_world", #[.some ⟨0⟩, .some ⟨11⟩]⟩
#guard word_class.bt.capture "test_123" = .some ⟨"test_123", #[.some ⟨0⟩, .some ⟨8⟩]⟩
#guard word_class.bt.capture "special@chars" = .some ⟨"special@chars", #[.some ⟨0⟩, .some ⟨7⟩]⟩

--
-- word boundary tests
--
def word_boundary_01 := Regex.parse! r##"\b"##

-- name = "wb1"
#guard word_boundary_01.capture "" = none
#guard word_boundary_01.bt.capture "" = none

-- name = "wb2"
#guard word_boundary_01.captureAll "a" = #[
  ⟨"a", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"a", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_01.bt.captureAll "a" = #[
  ⟨"a", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"a", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]

-- name = "wb3"
#guard word_boundary_01.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩
]
#guard word_boundary_01.bt.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩
]

def word_boundary_02 := Regex.parse! r##"^\b"##

-- name = "wb4"
#guard  word_boundary_02.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard  word_boundary_02.bt.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

def word_boundary_03 := Regex.parse! r##"\b$"##

-- name = "wb5"
#guard word_boundary_03.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩
]
#guard word_boundary_03.bt.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
  ⟨"ab", #[.some ⟨2⟩, .some ⟨2⟩]⟩
]

def word_boundary_04 := Regex.parse! r##"^\b$"##

-- name = "wb6"
#guard word_boundary_04.captureAll "ab" = #[]
#guard word_boundary_04.bt.captureAll "ab" = #[]

def word_boundary_05 := Regex.parse! r##"\bbar\b"##

-- name = "wb7"
#guard word_boundary_05.captureAll "nobar bar foo bar" = #[
  ⟨"nobar bar foo bar", #[.some ⟨6⟩, .some ⟨9⟩]⟩,
  ⟨"nobar bar foo bar", #[.some ⟨14⟩, .some ⟨17⟩]⟩
]
#guard word_boundary_05.bt.captureAll "nobar bar foo bar" = #[
  ⟨"nobar bar foo bar", #[.some ⟨6⟩, .some ⟨9⟩]⟩,
  ⟨"nobar bar foo bar", #[.some ⟨14⟩, .some ⟨17⟩]⟩
]

def word_boundary_06 := Regex.parse! r##"a\b"##

-- name = "wb8"
#guard word_boundary_06.captureAll "faoa x" = #[
  ⟨"faoa x", #[.some ⟨3⟩, .some ⟨4⟩]⟩
]
#guard word_boundary_06.bt.captureAll "faoa x" = #[
  ⟨"faoa x", #[.some ⟨3⟩, .some ⟨4⟩]⟩
]

def word_boundary_07 := Regex.parse! r##"\bbar"##

-- name = "wb9"
#guard word_boundary_07.captureAll "bar x" = #[
  ⟨"bar x", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_07.bt.captureAll "bar x" = #[
  ⟨"bar x", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

-- name = "wb10"
#guard word_boundary_07.captureAll "foo\nbar x" = #[
  ⟨"foo\nbar x", #[.some ⟨4⟩, .some ⟨7⟩]⟩
]
#guard word_boundary_07.bt.captureAll "foo\nbar x" = #[
  ⟨"foo\nbar x", #[.some ⟨4⟩, .some ⟨7⟩]⟩
]

def word_boundary_08 := Regex.parse! r##"bar\b"##

-- name = "wb11"
#guard word_boundary_08.captureAll "foobar" = #[
  ⟨"foobar", #[.some ⟨3⟩, .some ⟨6⟩]⟩
]
#guard word_boundary_08.bt.captureAll "foobar" = #[
  ⟨"foobar", #[.some ⟨3⟩, .some ⟨6⟩]⟩
]

-- name = "wb12"
#guard word_boundary_08.captureAll "foobar\nxxx" = #[
  ⟨"foobar\nxxx", #[.some ⟨3⟩, .some ⟨6⟩]⟩
]
#guard word_boundary_08.bt.captureAll "foobar\nxxx" = #[
  ⟨"foobar\nxxx", #[.some ⟨3⟩, .some ⟨6⟩]⟩
]

def word_boundary_09 := Regex.parse! r##"(?:foo|bar|[A-Z])\b"##

-- name = "wb13"
#guard word_boundary_09.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_09.bt.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

-- name = "wb14"
#guard word_boundary_09.captureAll "foo\n" = #[
  ⟨"foo\n", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_09.bt.captureAll "foo\n" = #[
  ⟨"foo\n", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

def word_boundary_10 := Regex.parse! r##"\b(?:foo|bar|[A-Z])"##

-- name = "wb15"
#guard word_boundary_10.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_10.bt.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

def word_boundary_11 := Regex.parse! r##"\b(?:foo|bar|[A-Z])\b"##

-- name = "wb16"
#guard word_boundary_11.captureAll "X" = #[
  ⟨"X", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_11.bt.captureAll "X" = #[
  ⟨"X", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

-- name = "wb17"
#guard word_boundary_11.captureAll "XY" = #[]
#guard word_boundary_11.bt.captureAll "XY" = #[]

-- name = "wb18"
#guard word_boundary_11.captureAll "bar" = #[
  ⟨"bar", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_11.bt.captureAll "bar" = #[
  ⟨"bar", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

-- name = "wb19"
#guard word_boundary_11.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_11.bt.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

-- name = "wb20"
#guard word_boundary_11.captureAll "foo\n" = #[
  ⟨"foo\n", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_11.bt.captureAll "foo\n" = #[
  ⟨"foo\n", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

-- name = "wb21"
#guard word_boundary_11.captureAll "ffoo bbar N x" = #[
  ⟨"ffoo bbar N x", #[.some ⟨10⟩, .some ⟨11⟩]⟩
]
#guard word_boundary_11.bt.captureAll "ffoo bbar N x" = #[
  ⟨"ffoo bbar N x", #[.some ⟨10⟩, .some ⟨11⟩]⟩
]

def word_boundary_12 := Regex.parse! r##"\b(?:fo|foo)\b"##

-- name = "wb22"
#guard word_boundary_12.captureAll "fo" = #[
  ⟨"fo", #[.some ⟨0⟩, .some ⟨2⟩]⟩
]
#guard word_boundary_12.bt.captureAll "fo" = #[
  ⟨"fo", #[.some ⟨0⟩, .some ⟨2⟩]⟩
]

-- name = "wb23"
#guard word_boundary_12.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_12.bt.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

def word_boundary_13 := Regex.parse! r##"\b\b"##

-- name = "wb24"
#guard word_boundary_13.captureAll "" = #[]
#guard word_boundary_13.bt.captureAll "" = #[]

-- name = "wb25"
#guard word_boundary_13.captureAll "a" = #[
  ⟨"a", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"a", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_13.bt.captureAll "a" = #[
  ⟨"a", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"a", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]

def word_boundary_14 := Regex.parse! r##"\b$"##

-- name = "wb26"
#guard word_boundary_14.captureAll "" = #[]
#guard word_boundary_14.bt.captureAll "" = #[]

-- name = "wb27"
#guard word_boundary_14.captureAll "x" = #[
  ⟨"x", #[.some ⟨1⟩, .some ⟨1⟩]⟩,
  ⟨"x", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_14.bt.captureAll "x" = #[
  ⟨"x", #[.some ⟨1⟩, .some ⟨1⟩]⟩,
  ⟨"x", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]

-- name = "wb28"
#guard word_boundary_14.captureAll "y x" = #[
  ⟨"y x", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
  ⟨"y x", #[.some ⟨3⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_14.bt.captureAll "y x" = #[
  ⟨"y x", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
  ⟨"y x", #[.some ⟨3⟩, .some ⟨3⟩]⟩
]

def word_boundary_15 := Regex.parse! r##"(?:\b).$"##

-- name = "wb29"
#guard word_boundary_15.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_15.bt.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

def word_boundary_16 := Regex.parse! r##"^\b(?:fo|foo)\b"##

-- name = "wb30"
#guard word_boundary_16.captureAll "fo" = #[
  ⟨"fo", #[.some ⟨0⟩, .some ⟨2⟩]⟩
]
#guard word_boundary_16.bt.captureAll "fo" = #[
  ⟨"fo", #[.some ⟨0⟩, .some ⟨2⟩]⟩
]

-- name = "wb31"
#guard word_boundary_16.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard word_boundary_16.bt.captureAll "foo" = #[
  ⟨"foo", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

def word_boundary_17 := Regex.parse! r##"^\b$"##

-- name = "wb32"
#guard word_boundary_17.captureAll "" = #[]
#guard word_boundary_17.bt.captureAll "" = #[]

-- name = "wb33"
#guard word_boundary_17.captureAll "x" = #[]
#guard word_boundary_17.bt.captureAll "x" = #[]

def word_boundary_18 := Regex.parse! r##"^(?:\b).$"##

-- name = "wb34"
#guard word_boundary_18.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_18.bt.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

def word_boundary_19 := Regex.parse! r##"^(?:\b).(?:\b)$"##

-- name = "wb35"
#guard word_boundary_19.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_19.bt.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

def word_boundary_20 := Regex.parse! r##"^^^^^\b$$$$$"##

-- name = "wb36"
#guard word_boundary_20.captureAll "" = #[]
#guard word_boundary_20.bt.captureAll "" = #[]

def word_boundary_21 := Regex.parse! r##"^^^^^(?:\b).$$$$$"##

-- name = "wb37"
#guard word_boundary_21.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_21.bt.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

def word_boundary_22 := Regex.parse! r##"^^^^^\b$$$$$"##

-- name = "wb38"
#guard word_boundary_22.captureAll "x" = #[]
#guard word_boundary_22.bt.captureAll "x" = #[]

def word_boundary_23 := Regex.parse! r##"^^^^^(?:\b\b\b).(?:\b\b\b)$$$$$"##

-- name = "wb39"
#guard word_boundary_23.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard word_boundary_23.bt.captureAll "x" = #[
  ⟨"x", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

def word_boundary_24 := Regex.parse! r##"(?:\b).+(?:\b)"##

-- name = "wb40"
#guard word_boundary_24.captureAll "$$abc$$" = #[
  ⟨"$$abc$$", #[.some ⟨2⟩, .some ⟨5⟩]⟩
]
#guard word_boundary_24.bt.captureAll "$$abc$$" = #[
  ⟨"$$abc$$", #[.some ⟨2⟩, .some ⟨5⟩]⟩
]

def word_boundary_25 := Regex.parse! r##"\b"##

-- name = "wb41"
#guard word_boundary_25.captureAll "a b c" = #[
  ⟨"a b c", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"a b c", #[.some ⟨1⟩, .some ⟨1⟩]⟩,
  ⟨"a b c", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
  ⟨"a b c", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
  ⟨"a b c", #[.some ⟨4⟩, .some ⟨4⟩]⟩,
  ⟨"a b c", #[.some ⟨5⟩, .some ⟨5⟩]⟩
]
#guard word_boundary_25.bt.captureAll "a b c" = #[
  ⟨"a b c", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"a b c", #[.some ⟨1⟩, .some ⟨1⟩]⟩,
  ⟨"a b c", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
  ⟨"a b c", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
  ⟨"a b c", #[.some ⟨4⟩, .some ⟨4⟩]⟩,
  ⟨"a b c", #[.some ⟨5⟩, .some ⟨5⟩]⟩
]

def word_boundary_26 := Regex.parse! r##"\bfoo\b"##

-- name = "wb42"
#guard word_boundary_26.captureAll "zzz foo zzz" = #[
  ⟨"zzz foo zzz", #[.some ⟨4⟩, .some ⟨7⟩]⟩
]
#guard word_boundary_26.bt.captureAll "zzz foo zzz" = #[
  ⟨"zzz foo zzz", #[.some ⟨4⟩, .some ⟨7⟩]⟩
]

def word_boundary_27 := Regex.parse! r##"\b^"##

-- name = "wb43"
#guard word_boundary_27.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard word_boundary_27.bt.captureAll "ab" = #[
  ⟨"ab", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

-- Non word boundary tests
-- Tests for \B. Note that \B is not allowed if UTF-8 mode is enabled, so we
-- have to disable it for most of these tests. This is because \B can match at
-- non-UTF-8 boundaries.

def non_word_boundary_01 := Regex.parse! r##"\Bfoo\B"##

-- name = "nb1"
#guard non_word_boundary_01.captureAll "n foo xfoox that" = #[
  ⟨"n foo xfoox that", #[.some ⟨7⟩, .some ⟨10⟩]⟩
]
#guard non_word_boundary_01.bt.captureAll "n foo xfoox that" = #[
  ⟨"n foo xfoox that", #[.some ⟨7⟩, .some ⟨10⟩]⟩
]

def non_word_boundary_02 := Regex.parse! r##"a\B"##

-- name = "nb2"
#guard non_word_boundary_02.captureAll "faoa x" = #[
  ⟨"faoa x", #[.some ⟨1⟩, .some ⟨2⟩]⟩
]
#guard non_word_boundary_02.bt.captureAll "faoa x" = #[
  ⟨"faoa x", #[.some ⟨1⟩, .some ⟨2⟩]⟩
]

def non_word_boundary_03 := Regex.parse! r##"\Bbar"##

-- name = "nb3"
#guard non_word_boundary_03.captureAll "bar x" = #[]
#guard non_word_boundary_03.bt.captureAll "bar x" = #[]

-- name = "nb4"
#guard non_word_boundary_03.captureAll "foo\nbar x" = #[]
#guard non_word_boundary_03.bt.captureAll "foo\nbar x" = #[]

def non_word_boundary_04 := Regex.parse! r##"bar\B"##

-- name = "nb5"
#guard non_word_boundary_04.captureAll "foobar" = #[]
#guard non_word_boundary_04.bt.captureAll "foobar" = #[]

-- name = "nb6"
#guard non_word_boundary_04.captureAll "foobar\nxxx" = #[]
#guard non_word_boundary_04.bt.captureAll "foobar\nxxx" = #[]

def non_word_boundary_05 := Regex.parse! r##"(?:foo|bar|[A-Z])\B"##

-- name = "nb7"
#guard non_word_boundary_05.captureAll "foox" = #[
  ⟨"foox", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]
#guard non_word_boundary_05.bt.captureAll "foox" = #[
  ⟨"foox", #[.some ⟨0⟩, .some ⟨3⟩]⟩
]

def non_word_boundary_06 := Regex.parse! r##"(?:foo|bar|[A-Z])\B"##

-- name = "nb8"
#guard non_word_boundary_06.captureAll "foo\n" = #[]
#guard non_word_boundary_06.bt.captureAll "foo\n" = #[]

def non_word_boundary_07 := Regex.parse! r##"\B"##

-- name = "nb9"
#guard non_word_boundary_07.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_07.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

def non_word_boundary_08 := Regex.parse! r##"\B"##

-- name = "nb10"
#guard non_word_boundary_08.captureAll "x" = #[]
#guard non_word_boundary_08.bt.captureAll "x" = #[]

def non_word_boundary_09 := Regex.parse! r##"\B(?:foo|bar|[A-Z])"##

-- name = "nb11"
#guard non_word_boundary_09.captureAll "foo" = #[]
#guard non_word_boundary_09.bt.captureAll "foo" = #[]

def non_word_boundary_10 := Regex.parse! r##"\B(?:foo|bar|[A-Z])\B"##

-- name = "nb12"
#guard non_word_boundary_10.captureAll "xXy" = #[
  ⟨"xXy", #[.some ⟨1⟩, .some ⟨2⟩]⟩
]
#guard non_word_boundary_10.bt.captureAll "xXy" = #[
  ⟨"xXy", #[.some ⟨1⟩, .some ⟨2⟩]⟩
]

-- name = "nb13"
#guard non_word_boundary_10.captureAll "XY" = #[]
#guard non_word_boundary_10.bt.captureAll "XY" = #[]

-- name = "nb14"
#guard non_word_boundary_10.captureAll "XYZ" = #[
  ⟨"XYZ", #[.some ⟨1⟩, .some ⟨2⟩]⟩
]
#guard non_word_boundary_10.bt.captureAll "XYZ" = #[
  ⟨"XYZ", #[.some ⟨1⟩, .some ⟨2⟩]⟩
]

-- name = "nb15"
#guard non_word_boundary_10.captureAll "abara" = #[
  ⟨"abara", #[.some ⟨1⟩, .some ⟨4⟩]⟩
]
#guard non_word_boundary_10.bt.captureAll "abara" = #[
  ⟨"abara", #[.some ⟨1⟩, .some ⟨4⟩]⟩
]

-- name = "nb16"
#guard non_word_boundary_10.captureAll "xfoo_" = #[
  ⟨"xfoo_", #[.some ⟨1⟩, .some ⟨4⟩]⟩
]
#guard non_word_boundary_10.bt.captureAll "xfoo_" = #[
  ⟨"xfoo_", #[.some ⟨1⟩, .some ⟨4⟩]⟩
]

-- name = "nb17"
#guard non_word_boundary_10.captureAll "xfoo\n" = #[]
#guard non_word_boundary_10.bt.captureAll "xfoo\n" = #[]

-- name = "nb18"
#guard non_word_boundary_10.captureAll "foo bar vNX" = #[
  ⟨"foo bar vNX", #[.some ⟨9⟩, .some ⟨10⟩]⟩
]
#guard non_word_boundary_10.bt.captureAll "foo bar vNX" = #[
  ⟨"foo bar vNX", #[.some ⟨9⟩, .some ⟨10⟩]⟩
]

def non_word_boundary_11 := Regex.parse! r##"\B(?:foo|fo)\B"##

-- name = "nb19"
#guard non_word_boundary_11.captureAll "xfoo" = #[
  ⟨"xfoo", #[.some ⟨1⟩, .some ⟨3⟩]⟩
]
#guard non_word_boundary_11.bt.captureAll "xfoo" = #[
  ⟨"xfoo", #[.some ⟨1⟩, .some ⟨3⟩]⟩
]

def non_word_boundary_12 := Regex.parse! r##"\B(?:foo|fo)\B"##

-- name = "nb20"
#guard non_word_boundary_12.captureAll "xfooo" = #[
  ⟨"xfooo", #[.some ⟨1⟩, .some ⟨4⟩]⟩
]
#guard non_word_boundary_12.bt.captureAll "xfooo" = #[
  ⟨"xfooo", #[.some ⟨1⟩, .some ⟨4⟩]⟩
]

def non_word_boundary_13 := Regex.parse! r##"\B\B"##

-- name = "nb21"
#guard non_word_boundary_13.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_13.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

-- name = "nb22"
#guard non_word_boundary_13.captureAll "x" = #[]
#guard non_word_boundary_13.bt.captureAll "x" = #[]

def non_word_boundary_14 := Regex.parse! r##"\B$"##

-- name = "nb23"
#guard non_word_boundary_14.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_14.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

-- name = "nb24"
#guard non_word_boundary_14.captureAll "x" = #[]
#guard non_word_boundary_14.bt.captureAll "x" = #[]

-- name = "nb25"
#guard non_word_boundary_14.captureAll "y x" = #[]
#guard non_word_boundary_14.bt.captureAll "y x" = #[]

def non_word_boundary_15 := Regex.parse! r##"\B.$"##

-- name = "nb26"
#guard non_word_boundary_15.captureAll "x" = #[]
#guard non_word_boundary_15.bt.captureAll "x" = #[]

def non_word_boundary_16 := Regex.parse! r##"^\B(?:fo|foo)\B"##

-- name = "nb27"
#guard non_word_boundary_16.captureAll "fo" = #[]
#guard non_word_boundary_16.bt.captureAll "fo" = #[]

-- name = "nb28"
#guard non_word_boundary_16.captureAll "foo" = #[]
#guard non_word_boundary_16.bt.captureAll "foo" = #[]

def non_word_boundary_17 := Regex.parse! r##"^\B"##

-- name = "nb29"
#guard non_word_boundary_17.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_17.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

-- name = "nb30"
#guard non_word_boundary_17.captureAll "x" = #[]
#guard non_word_boundary_17.bt.captureAll "x" = #[]

def non_word_boundary_18 := Regex.parse! r##"^\B\B"##

-- name = "nb31"
#guard non_word_boundary_18.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_18.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

-- name = "nb32"
#guard non_word_boundary_18.captureAll "x" = #[]
#guard non_word_boundary_18.bt.captureAll "x" = #[]

def non_word_boundary_19 := Regex.parse! r##"^\B$"##

-- name = "nb33"
#guard non_word_boundary_19.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_19.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

-- name = "nb34"
#guard non_word_boundary_19.captureAll "x" = #[]
#guard non_word_boundary_19.bt.captureAll "x" = #[]

def non_word_boundary_20 := Regex.parse! r##"^\B.$"##

-- name = "nb35"
#guard non_word_boundary_20.captureAll "x" = #[]
#guard non_word_boundary_20.bt.captureAll "x" = #[]

def non_word_boundary_21 := Regex.parse! r##"^\B.\B$"##

-- name = "nb36"
#guard non_word_boundary_21.captureAll "x" = #[]
#guard non_word_boundary_21.bt.captureAll "x" = #[]

def non_word_boundary_22 := Regex.parse! r##"^^^^^\B$$$$$"##

-- name = "nb37"
#guard non_word_boundary_22.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]
#guard non_word_boundary_22.bt.captureAll "" = #[
  ⟨"", #[.some ⟨0⟩, .some ⟨0⟩]⟩
]

def non_word_boundary_23 := Regex.parse! r##"^^^^^\B.$$$$$"##

-- name = "nb38"
#guard non_word_boundary_23.captureAll "x" = #[]
#guard non_word_boundary_23.bt.captureAll "x" = #[]

def non_word_boundary_24 := Regex.parse! r##"^^^^^\B$$$$$"##

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
def unicode_word_boundary_01 := Regex.parse! r##"\bx\b"##

-- name = "unicode1"
#guard unicode_word_boundary_01.captureAll "«x" = #[
  ⟨"«x", #[.some ⟨2⟩, .some ⟨3⟩]⟩
]
#guard unicode_word_boundary_01.bt.captureAll "«x" = #[
  ⟨"«x", #[.some ⟨2⟩, .some ⟨3⟩]⟩
]

-- name = "unicode1-only-ascii"
#guard unicode_word_boundary_01.captureAll "«x" = #[
  ⟨"«x", #[.some ⟨2⟩, .some ⟨3⟩]⟩
]
#guard unicode_word_boundary_01.bt.captureAll "«x" = #[
  ⟨"«x", #[.some ⟨2⟩, .some ⟨3⟩]⟩
]

-- name = "unicode2"
#guard unicode_word_boundary_01.captureAll "x»" = #[
  ⟨"x»", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard unicode_word_boundary_01.bt.captureAll "x»" = #[
  ⟨"x»", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

-- name = "unicode2-only-ascii"
#guard unicode_word_boundary_01.captureAll "x»" = #[
  ⟨"x»", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]
#guard unicode_word_boundary_01.bt.captureAll "x»" = #[
  ⟨"x»", #[.some ⟨0⟩, .some ⟨1⟩]⟩
]

-- ASCII word boundaries are completely oblivious to Unicode characters, so
-- even though β is a character, an ASCII \b treats it as a word boundary
-- when it is adjacent to another ASCII character. (The ASCII \b only looks
-- at the leading byte of β.) For Unicode \b, the tests are precisely inverted.

-- FIXME: This test is not working as expected.
-- name = "unicode3"
-- #eval unicode_word_boundary_01.captureAll "áxβ"
-- #guard unicode_word_boundary_01.captureAll "áxβ" = #[]
-- #guard unicode_word_boundary_01.bt.captureAll "áxβ" = #[]

-- name = "unicode3-only-ascii"
#guard unicode_word_boundary_01.captureAll "áxβ" = #[
  ⟨"áxβ", #[.some ⟨2⟩, .some ⟨3⟩]⟩
]
#guard unicode_word_boundary_01.bt.captureAll "áxβ" = #[
  ⟨"áxβ", #[.some ⟨2⟩, .some ⟨3⟩]⟩
]

def unicode_non_word_boundary_01 := Regex.parse! r##"\Bx\B"##

-- FIXME: This test is not working as expected.
-- name = "unicode4"
-- #eval unicode_word_boundary_02.captureAll "áxβ"
-- #guard unicode_word_boundary_02.captureAll "áxβ" = #[
--   ⟨"áxβ", #[.some ⟨2⟩, .some ⟨3⟩]⟩
-- ]
-- #guard unicode_word_boundary_02.bt.captureAll "áxβ" = #[
--   ⟨"áxβ", #[.some ⟨2⟩, .some ⟨3⟩]⟩
-- ]

-- name = "unicode4-only-ascii"
#guard unicode_non_word_boundary_01.captureAll "áxβ" = #[]
#guard unicode_non_word_boundary_01.bt.captureAll "áxβ" = #[]

-- The same as above, but with \b instead of \B as a sanity check.
def unicode_word_boundary_02 := Regex.parse! r##"\b"##

-- FIXME: This test is not working as expected.
-- -- name = "unicode5"
-- #eval unicode_word_boundary_02.captureAll "0\U0007EF5E"
-- #guard unicode_word_boundary_02.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨1⟩, .some ⟨1⟩]⟩
-- ]
-- #guard unicode_word_boundary_02.bt.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨1⟩, .some ⟨1⟩]⟩
-- ]

-- FIXME: This test is not working as expected.
-- -- name = "unicode5-only-ascii"
-- #eval unicode_word_boundary_02.captureAll "0\U0007EF5E"
-- #guard unicode_word_boundary_02.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨1⟩, .some ⟨1⟩]⟩
-- ]
-- #guard unicode_word_boundary_02.bt.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨1⟩, .some ⟨1⟩]⟩
-- ]

-- name = "unicode5-noutf8"
#guard unicode_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF" = #[
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]
#guard unicode_word_boundary_02.bt.captureAll "0\xFF\xFF\xFF\xFF" = #[
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]

-- name = "unicode5-noutf8-only-ascii"
#guard unicode_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF" = #[
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]
#guard unicode_word_boundary_02.bt.captureAll "0\xFF\xFF\xFF\xFF" = #[
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨0⟩, .some ⟨0⟩]⟩,
  ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨1⟩, .some ⟨1⟩]⟩
]

-- Weird special case to ensure that ASCII \B treats each individual code unit
-- as a non-word byte. (The specific codepoint is irrelevant. It's an arbitrary
-- codepoint that uses 4 bytes in its UTF-8 encoding and is not a member of the
-- \w character class.)

def unicode_non_word_boundary_02 := Regex.parse! r##"\B"##

-- FIXME: This test is not working as expected.
-- -- name = "unicode5-not"
-- #eval unicode_non_word_boundary_02.captureAll "0\U0007EF5E"
-- #guard unicode_non_word_boundary_02.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨5⟩, .some ⟨5⟩]⟩
-- ]
-- #guard unicode_non_word_boundary_02.bt.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨5⟩, .some ⟨5⟩]⟩
-- ]

-- FIXME: This test is not working as expected.
-- name = "unicode5-not-only-ascii"
-- #eval unicode_non_word_boundary_02.captureAll "0\U0007EF5E"
-- #guard unicode_non_word_boundary_02.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨4⟩, .some ⟨4⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨5⟩, .some ⟨5⟩]⟩
-- ]
-- #guard unicode_non_word_boundary_02.bt.captureAll "0\U0007EF5E" = #[
--   ⟨"0\U0007EF5E", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨4⟩, .some ⟨4⟩]⟩,
--   ⟨"0\U0007EF5E", #[.some ⟨5⟩, .some ⟨5⟩]⟩
-- ]

-- This gets no matches since \B only matches in the presence of valid UTF-8
-- when Unicode is enabled, even when UTF-8 mode is disabled.

-- FIXME: This test is not working as expected.
-- -- name = "unicode5-not-noutf8"
-- #eval unicode_non_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF"
-- #guard unicode_non_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF" = #[]
-- #guard unicode_non_word_boundary_02.bt.captureAll "0\xFF\xFF\xFF\xFF" = #[]

-- But this DOES get matches since \B in ASCII mode only looks at individual
-- bytes.

-- FIXME: This test is not working as expected.
-- name = "unicode5-not-noutf8-only-ascii"
-- #eval unicode_non_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF"
-- #guard unicode_non_word_boundary_02.captureAll "0\xFF\xFF\xFF\xFF" = #[
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨4⟩, .some ⟨4⟩]⟩,
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨5⟩, .some ⟨5⟩]⟩
-- ]
-- #guard unicode_non_word_boundary_02.bt.captureAll "0\xFF\xFF\xFF\xFF" = #[
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨2⟩, .some ⟨2⟩]⟩,
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨3⟩, .some ⟨3⟩]⟩,
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨4⟩, .some ⟨4⟩]⟩,
--   ⟨"0\xFF\xFF\xFF\xFF", #[.some ⟨5⟩, .some ⟨5⟩]⟩
-- ]

-- Some tests of no particular significance.
def unicode_word_boundary_03 := Regex.parse! r##"\b[0-9]+\b"##

-- name = "unicode6"
#guard unicode_word_boundary_03.captureAll "foo 123 bar 456 quux 789" = #[
  ⟨"foo 123 bar 456 quux 789", #[.some ⟨4⟩, .some ⟨7⟩]⟩,
  ⟨"foo 123 bar 456 quux 789", #[.some ⟨12⟩, .some ⟨15⟩]⟩,
  ⟨"foo 123 bar 456 quux 789", #[.some ⟨21⟩, .some ⟨24⟩]⟩
]
#guard unicode_word_boundary_03.bt.captureAll "foo 123 bar 456 quux 789" = #[
  ⟨"foo 123 bar 456 quux 789", #[.some ⟨4⟩, .some ⟨7⟩]⟩,
  ⟨"foo 123 bar 456 quux 789", #[.some ⟨12⟩, .some ⟨15⟩]⟩,
  ⟨"foo 123 bar 456 quux 789", #[.some ⟨21⟩, .some ⟨24⟩]⟩
]

-- name = "unicode7"
#guard unicode_word_boundary_03.captureAll "foo 123 bar a456 quux 789" = #[
  ⟨"foo 123 bar a456 quux 789", #[.some ⟨4⟩, .some ⟨7⟩]⟩,
  ⟨"foo 123 bar a456 quux 789", #[.some ⟨22⟩, .some ⟨25⟩]⟩
]
#guard unicode_word_boundary_03.bt.captureAll "foo 123 bar a456 quux 789" = #[
  ⟨"foo 123 bar a456 quux 789", #[.some ⟨4⟩, .some ⟨7⟩]⟩,
  ⟨"foo 123 bar a456 quux 789", #[.some ⟨22⟩, .some ⟨25⟩]⟩
]

-- name = "unicode8"
#guard unicode_word_boundary_03.captureAll "foo 123 bar 456a quux 789" = #[
  ⟨"foo 123 bar 456a quux 789", #[.some ⟨4⟩, .some ⟨7⟩]⟩,
  ⟨"foo 123 bar 456a quux 789", #[.some ⟨22⟩, .some ⟨25⟩]⟩
]
#guard unicode_word_boundary_03.bt.captureAll "foo 123 bar 456a quux 789" = #[
  ⟨"foo 123 bar 456a quux 789", #[.some ⟨4⟩, .some ⟨7⟩]⟩,
  ⟨"foo 123 bar 456a quux 789", #[.some ⟨22⟩, .some ⟨25⟩]⟩
]

-- A variant of the problem described here:
-- https://github.com/google/re2/blob/89567f5de5b23bb5ad0c26cbafc10bdc7389d1fa/re2/dfa.cc#L658-L667

def unicode_word_boundary_04 := Regex.parse! r##"(?:\b|%)+"##

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

private def Regex.splitTest (regex : Regex) (haystack : String) : Array String :=
  regex.split haystack |>.map Substring.toString

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
