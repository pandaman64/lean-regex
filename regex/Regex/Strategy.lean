module

public import Regex.NFA
public import Regex.Data.String

open String (Pos PosPlusOne)

@[expose]
public section

namespace Regex

class PosTracker (s : String) (α : Type) where
  empty : α
  write : α → Nat → Pos s → α

attribute [simp] PosTracker.empty PosTracker.write

namespace PosTracker

instance listTracker (s : String) : PosTracker s (List (Nat × Pos s)) where
  empty := []
  write update offset pos := update ++ [(offset, pos)]

instance vectorTracker (s : String) (size : Nat) : PosTracker s (Vector (PosPlusOne s) size) where
  empty := Vector.replicate size (.sentinel s)
  write buffer offset pos := Vector.setIfInBounds buffer offset (.pos pos)

end PosTracker

end Regex

end
