import Regex.Regex.Utilities
import Regex.Regex.Elab
import Regex.Backtracker

namespace Epsilon

def epsilon := Regex.parse! r##""##
#guard epsilon.find "" = .some (⟨0⟩, ⟨0⟩)

def star := Regex.parse! r##"a*"##
#guard star.find "" = .some (⟨0⟩, ⟨0⟩)

end Epsilon

namespace Priority

def re := Regex.parse! r##"bool|boolean"##
#guard re.find "boolean" = .some (⟨0⟩, ⟨4⟩)

def re' := Regex.parse! r##"|x"##
#guard re'.find "x" = .some (⟨0⟩, ⟨0⟩)

def re'' := Regex.parse! r##"x|"##
#guard re''.find "x" = .some (⟨0⟩, ⟨1⟩)

def empty_110 := Regex.parse! r##"b|"##
-- Why does only Rust skip (⟨2⟩, ⟨2⟩)? https://regex101.com/r/ZQcPeh/1
-- #guard re'''.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]
#guard empty_110.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨2⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]

def empty_310 := Regex.parse! r##"b||"##
-- Why does only Rust skip (⟨2⟩, ⟨2⟩)? https://regex101.com/r/j7z8gd/1
-- #guard re'''.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]
#guard empty_110.findAll "abc" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨2⟩), (⟨2⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]

def empty_600 := Regex.parse! r##"(?:|a)*"##
#eval empty_600.findAll "aaa"
-- BUG: we report [(⟨0⟩, ⟨3⟩), (⟨3⟩, ⟨3⟩)]
-- #guard empty_600.findAll "aaa" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨1⟩), (⟨2⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]

def empty_610 := Regex.parse! r##"(?:|a)+"##
#eval empty_610.findAll "aaa"
-- BUG: we report [(⟨0⟩, ⟨3⟩), (⟨3⟩, ⟨3⟩)]
-- #guard empty_610.findAll "aaa" = #[(⟨0⟩, ⟨0⟩), (⟨1⟩, ⟨1⟩), (⟨2⟩, ⟨2⟩), (⟨3⟩, ⟨3⟩)]

end Priority

namespace Backtracker

def simple_char := Regex.parse! r##"a"##
#guard Regex.Backtracker.captureNextBuf simple_char.nfa simple_char.wf 2 "a".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]
#guard Regex.Backtracker.captureNextBuf simple_char.nfa simple_char.wf 2 "b".mkIterator = .none

def simple_concat := Regex.parse! r##"ab"##
#guard Regex.Backtracker.captureNextBuf simple_concat.nfa simple_concat.wf 2 "ab".mkIterator = .some #v[.some ⟨0⟩, .some ⟨2⟩]
#guard Regex.Backtracker.captureNextBuf simple_concat.nfa simple_concat.wf 2 "ac".mkIterator = .none

def simple_alt := Regex.parse! r##"a|b"##
#guard Regex.Backtracker.captureNextBuf simple_alt.nfa simple_alt.wf 2 "a".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]
#guard Regex.Backtracker.captureNextBuf simple_alt.nfa simple_alt.wf 2 "b".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]
#guard Regex.Backtracker.captureNextBuf simple_alt.nfa simple_alt.wf 2 "c".mkIterator = .none

def simple_star := Regex.parse! r##"a*"##
#guard Regex.Backtracker.captureNextBuf simple_star.nfa simple_star.wf 2 "".mkIterator = .some #v[.some ⟨0⟩, .some ⟨0⟩]
#guard Regex.Backtracker.captureNextBuf simple_star.nfa simple_star.wf 2 "a".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]
#guard Regex.Backtracker.captureNextBuf simple_star.nfa simple_star.wf 2 "aa".mkIterator = .some #v[.some ⟨0⟩, .some ⟨2⟩]

def complex_pattern := Regex.parse! r##"(a|b)*c"##
#guard Regex.Backtracker.captureNextBuf complex_pattern.nfa complex_pattern.wf 2 "c".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]
#guard Regex.Backtracker.captureNextBuf complex_pattern.nfa complex_pattern.wf 2 "ac".mkIterator = .some #v[.some ⟨0⟩, .some ⟨2⟩]
#guard Regex.Backtracker.captureNextBuf complex_pattern.nfa complex_pattern.wf 2 "bc".mkIterator = .some #v[.some ⟨0⟩, .some ⟨2⟩]
#guard Regex.Backtracker.captureNextBuf complex_pattern.nfa complex_pattern.wf 2 "aabbczy".mkIterator = .some #v[.some ⟨0⟩, .some ⟨5⟩]
#guard Regex.Backtracker.captureNextBuf complex_pattern.nfa complex_pattern.wf 2 "d".mkIterator = .none

def nested_groups := Regex.parse! r##"(a(b(c)))"##
#guard Regex.Backtracker.captureNextBuf nested_groups.nfa nested_groups.wf 2 "abc".mkIterator = .some #v[.some ⟨0⟩, .some ⟨3⟩]
#guard Regex.Backtracker.captureNextBuf nested_groups.nfa nested_groups.wf 2 "ab".mkIterator = .none
#guard Regex.Backtracker.captureNextBuf nested_groups.nfa nested_groups.wf 2 "a".mkIterator = .none

def complex_quantifiers := Regex.parse! r##"a{2,4}b{1,3}"##
#guard Regex.Backtracker.captureNextBuf complex_quantifiers.nfa complex_quantifiers.wf 2 "aab".mkIterator = .some #v[.some ⟨0⟩, .some ⟨3⟩]
#guard Regex.Backtracker.captureNextBuf complex_quantifiers.nfa complex_quantifiers.wf 2 "aaabbb".mkIterator = .some #v[.some ⟨0⟩, .some ⟨6⟩]
#guard Regex.Backtracker.captureNextBuf complex_quantifiers.nfa complex_quantifiers.wf 2 "ab".mkIterator = .none
#guard Regex.Backtracker.captureNextBuf complex_quantifiers.nfa complex_quantifiers.wf 2 "aabbb".mkIterator = .some #v[.some ⟨0⟩, .some ⟨5⟩]

def alternation_with_groups := Regex.parse! r##"(ab|cd)(ef|gh)"##
#guard Regex.Backtracker.captureNextBuf alternation_with_groups.nfa alternation_with_groups.wf 2 "abef".mkIterator = .some #v[.some ⟨0⟩, .some ⟨4⟩]
#guard Regex.Backtracker.captureNextBuf alternation_with_groups.nfa alternation_with_groups.wf 2 "cdgh".mkIterator = .some #v[.some ⟨0⟩, .some ⟨4⟩]
#guard Regex.Backtracker.captureNextBuf alternation_with_groups.nfa alternation_with_groups.wf 2 "abgh".mkIterator = .some #v[.some ⟨0⟩, .some ⟨4⟩]
#guard Regex.Backtracker.captureNextBuf alternation_with_groups.nfa alternation_with_groups.wf 2 "cdef".mkIterator = .some #v[.some ⟨0⟩, .some ⟨4⟩]

def complex_character_classes := Regex.parse! r##"[a-zA-Z0-9_]+@[a-zA-Z0-9]+\.[a-zA-Z]{2,}"##
#guard Regex.Backtracker.captureNextBuf complex_character_classes.nfa complex_character_classes.wf 2 "test@example.com".mkIterator = .some #v[.some ⟨0⟩, .some ⟨16⟩]
#guard Regex.Backtracker.captureNextBuf complex_character_classes.nfa complex_character_classes.wf 2 "user123@domain.org".mkIterator = .some #v[.some ⟨0⟩, .some ⟨18⟩]
#guard Regex.Backtracker.captureNextBuf complex_character_classes.nfa complex_character_classes.wf 2 "invalid@email".mkIterator = .none
#guard Regex.Backtracker.captureNextBuf complex_character_classes.nfa complex_character_classes.wf 2 "test@.com".mkIterator = .none

def nested_quantifiers := Regex.parse! r##"(a+)*b"##
#guard Regex.Backtracker.captureNextBuf nested_quantifiers.nfa nested_quantifiers.wf 2 "b".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]
#guard Regex.Backtracker.captureNextBuf nested_quantifiers.nfa nested_quantifiers.wf 2 "ab".mkIterator = .some #v[.some ⟨0⟩, .some ⟨2⟩]
#guard Regex.Backtracker.captureNextBuf nested_quantifiers.nfa nested_quantifiers.wf 2 "aaab".mkIterator = .some #v[.some ⟨0⟩, .some ⟨4⟩]
#guard Regex.Backtracker.captureNextBuf nested_quantifiers.nfa nested_quantifiers.wf 2 "a".mkIterator = .none
#guard Regex.Backtracker.captureNextBuf nested_quantifiers.nfa nested_quantifiers.wf 2 "ba".mkIterator = .some #v[.some ⟨0⟩, .some ⟨1⟩]

end Backtracker
