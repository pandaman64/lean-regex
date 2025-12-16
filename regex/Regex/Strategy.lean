import Regex.NFA

set_option autoImplicit false

open String (Pos PosPlusOne)

namespace Regex

structure Strategy (s : String) where
  Update : Type
  empty : Update
  write : Update → Nat → Pos s → Update

abbrev Buffer (s : String) (size : Nat) := Vector (PosPlusOne s) size

def Buffer.empty {s : String} {size : Nat} : Buffer s size := Vector.replicate size (.sentinel s)

def BufferStrategy (s : String) (size : Nat) : Strategy s where
  Update := Buffer s size
  empty := Buffer.empty
  write buffer offset pos := Vector.setIfInBounds buffer offset (.pos pos)

local instance {s} : Repr (Pos s) where
  reprPrec p n := reprPrec p.offset n

instance {s size} : Repr (BufferStrategy s size).Update := inferInstanceAs (Repr (Vector (PosPlusOne s) size))

instance {s size} : Inhabited (BufferStrategy s size).Update := inferInstanceAs (Inhabited (Vector (PosPlusOne s) size))

instance {s size} : DecidableEq (BufferStrategy s size).Update := inferInstanceAs (DecidableEq (Vector (PosPlusOne s) size))

instance {s size} : GetElem (BufferStrategy s size).Update Nat (PosPlusOne s) (fun _ i => i < size) :=
  inferInstanceAs (GetElem (Vector (PosPlusOne s) size) Nat (PosPlusOne s) _)

@[simp]
theorem BufferStrategy.update_def {s size} : (BufferStrategy s size).Update = Buffer s size := rfl

@[simp]
theorem BufferStrategy.empty_def {s size} : (BufferStrategy s size).empty = Buffer.empty := rfl

@[simp]
theorem BufferStrategy.write_def {s size buffer offset pos} :
  (BufferStrategy s size).write buffer offset pos = Vector.setIfInBounds buffer offset (.pos pos) := rfl

/--
This strategy is inefficient and used only for proofs.
-/
def HistoryStrategy (s : String) : Strategy s where
  Update := List (Nat × Pos s)
  empty := []
  write update offset pos := update ++ [(offset, pos)]

@[simp]
theorem HistoryStrategy.update_def {s} : (HistoryStrategy s).Update = List (Nat × Pos s) := rfl

@[simp]
theorem HistoryStrategy.empty_def {s} : (HistoryStrategy s).empty = [] := rfl

@[simp]
theorem HistoryStrategy.write_def {s update offset pos} :
  (HistoryStrategy s).write update offset pos = update.append [(offset, pos)] := rfl

end Regex
