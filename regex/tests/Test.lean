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

-- BUG: we don't handle empty matches correctly.
-- def re' := Regex.parse! r##"|x"##
-- #guard re'.find "x" = .some (⟨0⟩, ⟨0⟩)

end Priority
