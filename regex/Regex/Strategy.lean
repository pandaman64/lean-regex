import Regex.NFA

set_option autoImplicit false

open String (ValidPos)

namespace Regex

structure Strategy (s : String) where
  Update : Type
  empty : Update
  write : Update → Nat → ValidPos s → Update

abbrev Buffer (s : String) (size : Nat) := Vector (Option (ValidPos s)) size

def Buffer.empty {s : String} {size : Nat} : Buffer s size := Vector.replicate size none

def BufferStrategy (s : String) (size : Nat) : Strategy s where
  Update := Buffer s size
  empty := Buffer.empty
  write buffer offset pos := Vector.setIfInBounds buffer offset pos

local instance {s} : Repr (ValidPos s) where
  reprPrec p n := reprPrec p.offset n

instance {s size} : Repr (BufferStrategy s size).Update := inferInstanceAs (Repr (Vector (Option (ValidPos s)) size))

instance {s size} : Inhabited (BufferStrategy s size).Update := inferInstanceAs (Inhabited (Vector (Option (ValidPos s)) size))

instance {s size} : DecidableEq (BufferStrategy s size).Update := inferInstanceAs (DecidableEq (Vector (Option (ValidPos s)) size))

instance {s size} : GetElem (BufferStrategy s size).Update Nat (Option (ValidPos s)) (fun _ i => i < size) :=
  inferInstanceAs (GetElem (Vector (Option (ValidPos s)) size) Nat (Option (ValidPos s)) _)

@[simp]
theorem BufferStrategy.update_def {s size} : (BufferStrategy s size).Update = Buffer s size := rfl

@[simp]
theorem BufferStrategy.empty_def {s size} : (BufferStrategy s size).empty = Buffer.empty := rfl

@[simp]
theorem BufferStrategy.write_def {s size buffer offset pos} :
  (BufferStrategy s size).write buffer offset pos = Vector.setIfInBounds buffer offset pos := rfl

/--
This strategy is inefficient and used only for proofs.
-/
def HistoryStrategy (s : String) : Strategy s where
  Update := List (Nat × ValidPos s)
  empty := []
  write update offset pos := update ++ [(offset, pos)]

@[simp]
theorem HistoryStrategy.update_def {s} : (HistoryStrategy s).Update = List (Nat × ValidPos s) := rfl

@[simp]
theorem HistoryStrategy.empty_def {s} : (HistoryStrategy s).empty = [] := rfl

@[simp]
theorem HistoryStrategy.write_def {s update offset pos} :
  (HistoryStrategy s).write update offset pos = update.append [(offset, pos)] := rfl

end Regex
