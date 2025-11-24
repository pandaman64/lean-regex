import Regex.NFA

set_option autoImplicit false

open String (Pos)

namespace Regex

structure Strategy where
  Update : Type
  empty : Update
  write : Update → Nat → Pos.Raw → Update

abbrev Buffer (size : Nat) := Vector (Option Pos.Raw) size

def Buffer.empty {size : Nat} : Buffer size := Vector.replicate size none

def BufferStrategy (size : Nat) : Strategy where
  Update := Buffer size
  empty := Buffer.empty
  write buffer offset pos := Vector.setIfInBounds buffer offset pos

instance {size} : Repr (BufferStrategy size).Update := inferInstanceAs (Repr (Vector (Option Pos.Raw) size))

instance {size} : Inhabited (BufferStrategy size).Update := inferInstanceAs (Inhabited (Vector (Option Pos.Raw) size))

instance {size} : DecidableEq (BufferStrategy size).Update := inferInstanceAs (DecidableEq (Vector (Option Pos.Raw) size))

instance {size} : GetElem (BufferStrategy size).Update Nat (Option Pos.Raw) (fun _ i => i < size) :=
  inferInstanceAs (GetElem (Vector (Option Pos.Raw) size) Nat (Option Pos.Raw) _)

@[simp]
theorem BufferStrategy.update_def {size : Nat} : (BufferStrategy size).Update = Buffer size := rfl

@[simp]
theorem BufferStrategy.empty_def {size : Nat} : (BufferStrategy size).empty = Buffer.empty := rfl

@[simp]
theorem BufferStrategy.write_def {size buffer offset pos} :
  (BufferStrategy size).write buffer offset pos = Vector.setIfInBounds buffer offset pos := rfl

/--
This strategy is inefficient and used only for proofs.
-/
def HistoryStrategy : Strategy where
  Update := List (Nat × Pos.Raw)
  empty := []
  write update offset pos := update ++ [(offset, pos)]

@[simp]
theorem HistoryStrategy.update_def : HistoryStrategy.Update = List (Nat × Pos.Raw) := rfl

@[simp]
theorem HistoryStrategy.empty_def : HistoryStrategy.empty = [] := rfl

@[simp]
theorem HistoryStrategy.write_def {update : List (Nat × Pos.Raw)} {offset : Nat} {pos : Pos.Raw} :
  HistoryStrategy.write update offset pos = update ++ [(offset, pos)] := rfl

end Regex
