import Regex.NFA

set_option autoImplicit false

open String (Pos)

namespace Regex

structure Strategy where
  Update : Type
  empty : Update
  write : Update → Nat → Pos → Update

abbrev Buffer (size : Nat) := Vector (Option Pos) size

def Buffer.empty {size : Nat} : Buffer size := Vector.mkVector size none

def BufferStrategy (size : Nat) : Strategy where
  Update := Buffer size
  empty := Buffer.empty
  write buffer offset pos := Vector.setIfInBounds buffer offset pos

instance {size} : Repr (BufferStrategy size).Update := inferInstanceAs (Repr (Vector (Option Pos) size))

instance {size} : Inhabited (BufferStrategy size).Update := inferInstanceAs (Inhabited (Vector (Option Pos) size))

instance {size} : DecidableEq (BufferStrategy size).Update := inferInstanceAs (DecidableEq (Vector (Option Pos) size))

instance {size} : GetElem (BufferStrategy size).Update Nat (Option Pos) (fun _ i => i < size) :=
  inferInstanceAs (GetElem (Vector (Option Pos) size) Nat (Option Pos) _)

/--
This strategy is inefficient and used only for proofs.
-/
def HistoryStrategy : Strategy where
  Update := List (Nat × Pos)
  empty := []
  write update offset pos := update ++ [(offset, pos)]

end Regex
