import Regex.Regex.Utilities
import Regex.Regex.Elab
import Regex.Backtracker

namespace Epsilon

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
#guard simple_char.capture "a" = .some ⟨#[.some ⟨"a", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_char.capture "b" = .none
#guard simple_char.bt.capture "a" = .some ⟨#[.some ⟨"a", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_char.bt.capture "b" = .none

def simple_concat := Regex.parse! r##"ab"##
#guard simple_concat.capture "ab" = .some ⟨#[.some ⟨"ab", ⟨0⟩, ⟨2⟩⟩]⟩
#guard simple_concat.capture "ac" = .none
#guard simple_concat.bt.capture "ab" = .some ⟨#[.some ⟨"ab", ⟨0⟩, ⟨2⟩⟩]⟩
#guard simple_concat.bt.capture "ac" = .none

def simple_alt := Regex.parse! r##"a|b"##
#guard simple_alt.capture "a" = .some ⟨#[.some ⟨"a", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_alt.capture "b" = .some ⟨#[.some ⟨"b", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_alt.capture "c" = .none
#guard simple_alt.bt.capture "a" = .some ⟨#[.some ⟨"a", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_alt.bt.capture "b" = .some ⟨#[.some ⟨"b", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_alt.bt.capture "c" = .none

def simple_star := Regex.parse! r##"a*"##
#guard simple_star.capture "" = .some ⟨#[.some ⟨"", ⟨0⟩, ⟨0⟩⟩]⟩
#guard simple_star.capture "a" = .some ⟨#[.some ⟨"a", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_star.capture "aa" = .some ⟨#[.some ⟨"aa", ⟨0⟩, ⟨2⟩⟩]⟩
#guard simple_star.bt.capture "" = .some ⟨#[.some ⟨"", ⟨0⟩, ⟨0⟩⟩]⟩
#guard simple_star.bt.capture "a" = .some ⟨#[.some ⟨"a", ⟨0⟩, ⟨1⟩⟩]⟩
#guard simple_star.bt.capture "aa" = .some ⟨#[.some ⟨"aa", ⟨0⟩, ⟨2⟩⟩]⟩

def complex_pattern := Regex.parse! r##"(a|b)*c"##
#guard complex_pattern.capture "c" = .some ⟨#[.some ⟨"c", ⟨0⟩, ⟨1⟩⟩, .none]⟩
#guard complex_pattern.capture "ac" = .some ⟨#[.some ⟨"ac", ⟨0⟩, ⟨2⟩⟩, .some ⟨"ac", ⟨0⟩, ⟨1⟩⟩]⟩
#guard complex_pattern.capture "bc" = .some ⟨#[.some ⟨"bc", ⟨0⟩, ⟨2⟩⟩, .some ⟨"bc", ⟨0⟩, ⟨1⟩⟩]⟩
#guard complex_pattern.capture "xyzaabbczy" = .some ⟨#[.some ⟨"xyzaabbczy", ⟨3⟩, ⟨8⟩⟩, .some ⟨"xyzaabbczy", ⟨6⟩, ⟨7⟩⟩]⟩
#guard complex_pattern.capture "d" = .none
#guard complex_pattern.bt.capture "c" = .some ⟨#[.some ⟨"c", ⟨0⟩, ⟨1⟩⟩, .none]⟩
#guard complex_pattern.bt.capture "ac" = .some ⟨#[.some ⟨"ac", ⟨0⟩, ⟨2⟩⟩, .some ⟨"ac", ⟨0⟩, ⟨1⟩⟩]⟩
#guard complex_pattern.bt.capture "bc" = .some ⟨#[.some ⟨"bc", ⟨0⟩, ⟨2⟩⟩, .some ⟨"bc", ⟨0⟩, ⟨1⟩⟩]⟩
#guard complex_pattern.bt.capture "xyzaabbczy" = .some ⟨#[.some ⟨"xyzaabbczy", ⟨3⟩, ⟨8⟩⟩, .some ⟨"xyzaabbczy", ⟨6⟩, ⟨7⟩⟩]⟩
#guard complex_pattern.bt.capture "d" = .none

def nested_groups := Regex.parse! r##"(a(b(c)))"##
#guard nested_groups.capture "abc" = .some ⟨#[.some ⟨"abc", ⟨0⟩, ⟨3⟩⟩, .some ⟨"abc", ⟨0⟩, ⟨3⟩⟩, .some ⟨"abc", ⟨1⟩, ⟨3⟩⟩, .some ⟨"abc", ⟨2⟩, ⟨3⟩⟩]⟩
#guard nested_groups.capture "ab" = .none
#guard nested_groups.capture "a" = .none
#guard nested_groups.bt.capture "abc" = .some ⟨#[.some ⟨"abc", ⟨0⟩, ⟨3⟩⟩, .some ⟨"abc", ⟨0⟩, ⟨3⟩⟩, .some ⟨"abc", ⟨1⟩, ⟨3⟩⟩, .some ⟨"abc", ⟨2⟩, ⟨3⟩⟩]⟩
#guard nested_groups.bt.capture "ab" = .none
#guard nested_groups.bt.capture "a" = .none

def complex_quantifiers := Regex.parse! r##"a{2,4}b{1,3}"##
#guard complex_quantifiers.capture "aab" = .some ⟨#[.some ⟨"aab", ⟨0⟩, ⟨3⟩⟩]⟩
#guard complex_quantifiers.capture "aaabbb" = .some ⟨#[.some ⟨"aaabbb", ⟨0⟩, ⟨6⟩⟩]⟩
#guard complex_quantifiers.capture "ab" = .none
#guard complex_quantifiers.capture "aabbb" = .some ⟨#[.some ⟨"aabbb", ⟨0⟩, ⟨5⟩⟩]⟩
#guard complex_quantifiers.bt.capture "aab" = .some ⟨#[.some ⟨"aab", ⟨0⟩, ⟨3⟩⟩]⟩
#guard complex_quantifiers.bt.capture "aaabbb" = .some ⟨#[.some ⟨"aaabbb", ⟨0⟩, ⟨6⟩⟩]⟩
#guard complex_quantifiers.bt.capture "ab" = .none
#guard complex_quantifiers.bt.capture "aabbb" = .some ⟨#[.some ⟨"aabbb", ⟨0⟩, ⟨5⟩⟩]⟩

def alternation_with_groups := Regex.parse! r##"(ab|cd)(ef|gh)"##
#guard alternation_with_groups.capture "abef" = .some ⟨#[.some ⟨"abef", ⟨0⟩, ⟨4⟩⟩, .some ⟨"abef", ⟨0⟩, ⟨2⟩⟩, .some ⟨"abef", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.capture "cdgh" = .some ⟨#[.some ⟨"cdgh", ⟨0⟩, ⟨4⟩⟩, .some ⟨"cdgh", ⟨0⟩, ⟨2⟩⟩, .some ⟨"cdgh", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.capture "abgh" = .some ⟨#[.some ⟨"abgh", ⟨0⟩, ⟨4⟩⟩, .some ⟨"abgh", ⟨0⟩, ⟨2⟩⟩, .some ⟨"abgh", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.capture "cdef" = .some ⟨#[.some ⟨"cdef", ⟨0⟩, ⟨4⟩⟩, .some ⟨"cdef", ⟨0⟩, ⟨2⟩⟩, .some ⟨"cdef", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.bt.capture "abef" = .some ⟨#[.some ⟨"abef", ⟨0⟩, ⟨4⟩⟩, .some ⟨"abef", ⟨0⟩, ⟨2⟩⟩, .some ⟨"abef", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.bt.capture "cdgh" = .some ⟨#[.some ⟨"cdgh", ⟨0⟩, ⟨4⟩⟩, .some ⟨"cdgh", ⟨0⟩, ⟨2⟩⟩, .some ⟨"cdgh", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.bt.capture "abgh" = .some ⟨#[.some ⟨"abgh", ⟨0⟩, ⟨4⟩⟩, .some ⟨"abgh", ⟨0⟩, ⟨2⟩⟩, .some ⟨"abgh", ⟨2⟩, ⟨4⟩⟩]⟩
#guard alternation_with_groups.bt.capture "cdef" = .some ⟨#[.some ⟨"cdef", ⟨0⟩, ⟨4⟩⟩, .some ⟨"cdef", ⟨0⟩, ⟨2⟩⟩, .some ⟨"cdef", ⟨2⟩, ⟨4⟩⟩]⟩

def complex_character_classes := Regex.parse! r##"[a-zA-Z0-9_]+@[a-zA-Z0-9]+\.[a-zA-Z]{2,}"##
#guard complex_character_classes.capture "test@example.com" = .some ⟨#[.some ⟨"test@example.com", ⟨0⟩, ⟨16⟩⟩]⟩
#guard complex_character_classes.capture "user123@domain.org" = .some ⟨#[.some ⟨"user123@domain.org", ⟨0⟩, ⟨18⟩⟩]⟩
#guard complex_character_classes.capture "invalid@email" = .none
#guard complex_character_classes.capture "test@.com" = .none
#guard complex_character_classes.bt.capture "test@example.com" = .some ⟨#[.some ⟨"test@example.com", ⟨0⟩, ⟨16⟩⟩]⟩
#guard complex_character_classes.bt.capture "user123@domain.org" = .some ⟨#[.some ⟨"user123@domain.org", ⟨0⟩, ⟨18⟩⟩]⟩
#guard complex_character_classes.bt.capture "invalid@email" = .none
#guard complex_character_classes.bt.capture "test@.com" = .none

def nested_quantifiers := Regex.parse! r##"(a+)*b"##
#guard nested_quantifiers.capture "b" = .some ⟨#[.some ⟨"b", ⟨0⟩, ⟨1⟩⟩, .none]⟩
#guard nested_quantifiers.capture "ab" = .some ⟨#[.some ⟨"ab", ⟨0⟩, ⟨2⟩⟩, .some ⟨"ab", ⟨0⟩, ⟨1⟩⟩]⟩
#guard nested_quantifiers.capture "aaab" = .some ⟨#[.some ⟨"aaab", ⟨0⟩, ⟨4⟩⟩, .some ⟨"aaab", ⟨0⟩, ⟨3⟩⟩]⟩
#guard nested_quantifiers.capture "a" = .none
#guard nested_quantifiers.capture "ba" = .some ⟨#[.some ⟨"ba", ⟨0⟩, ⟨1⟩⟩, .none]⟩
#guard nested_quantifiers.bt.capture "b" = .some ⟨#[.some ⟨"b", ⟨0⟩, ⟨1⟩⟩, .none]⟩
#guard nested_quantifiers.bt.capture "ab" = .some ⟨#[.some ⟨"ab", ⟨0⟩, ⟨2⟩⟩, .some ⟨"ab", ⟨0⟩, ⟨1⟩⟩]⟩
#guard nested_quantifiers.bt.capture "aaab" = .some ⟨#[.some ⟨"aaab", ⟨0⟩, ⟨4⟩⟩, .some ⟨"aaab", ⟨0⟩, ⟨3⟩⟩]⟩
#guard nested_quantifiers.bt.capture "a" = .none
#guard nested_quantifiers.bt.capture "ba" = .some ⟨#[.some ⟨"ba", ⟨0⟩, ⟨1⟩⟩, .none]⟩

def alt_in_alt_100 := re! r##"ab?|$"##
#eval alt_in_alt_100.captureAll "az"
#eval alt_in_alt_100.bt.captureAll "az"

end Comparison
