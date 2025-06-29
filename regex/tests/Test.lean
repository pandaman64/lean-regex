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
