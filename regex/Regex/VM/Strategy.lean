import Regex.Data.SparseSet
import Regex.NFA

set_option autoImplicit false

open Regex.Data (SparseSet)
open String (Pos)

namespace Regex.VM

class Strategy where
  Update : Type
  empty : Update
  set : Update → Nat → Pos → Update

abbrev Buffer (size : Nat) := Vector (Option Pos) size

def Buffer.empty {size : Nat} : Buffer size := Vector.mkVector size none

structure SearchState [σ : Strategy] (nfa : NFA) where
  states : SparseSet nfa.nodes.size
  updates : Vector σ.Update nfa.nodes.size

abbrev εStack [σ : Strategy] (nfa : NFA) := List (σ.Update × Fin nfa.nodes.size)

def BufferStrategy (size : Nat) : Strategy where
  Update := Buffer size
  empty := Buffer.empty
  set buffer offset pos := Vector.setIfInBounds buffer offset pos

end Regex.VM
