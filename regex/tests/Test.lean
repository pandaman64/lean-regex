import Regex.Regex.Utilities
import Regex.Regex.Elab

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
