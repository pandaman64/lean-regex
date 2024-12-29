import Regex.Data.SparseSet
import Regex.NFA

set_option autoImplicit false

open Regex (NFA)
open Regex.Data (SparseSet Vec)
open String (Pos)

namespace Regex.VM

structure SearchState' (nfa : NFA) where
  states : SparseSet nfa.nodes.size
  updates : Vec (List (Nat × Pos)) nfa.nodes.size

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
def WriteUpdate {nfa : NFA} (i : Fin nfa.nodes.size) : Prop :=
  match nfa[i] with
  | .done | .char _ _ | .sparse _ _ => True
  | _ => False

end Regex.VM
