import Regex.Data.SparseSet
import Regex.NFA

set_option autoImplicit false

open Regex.Data (SparseSet)
open String (Pos)

namespace Regex.VM

structure Strategy where
  Update : Type
  empty : Update
  write : Update → Nat → Pos → Update

abbrev Buffer (size : Nat) := Vector (Option Pos) size

def Buffer.empty {size : Nat} : Buffer size := Vector.mkVector size none

structure SearchState (σ : Strategy) (nfa : NFA) where
  states : SparseSet nfa.nodes.size
  updates : Vector σ.Update nfa.nodes.size

abbrev εStack (σ : Strategy) (nfa : NFA) := List (σ.Update × Fin nfa.nodes.size)

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
This strategy is used only for proofs and inefficient.
-/
def HistoryStrategy : Strategy where
  Update := List (Nat × Pos)
  empty := []
  write update offset pos := update ++ [(offset, pos)]

end Regex.VM
