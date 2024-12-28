import Regex.NFA

namespace Regex.VM

/--
As an optimization, we write the updates to the buffer only when the state is done, a character, or a sparse state.
-/
def WriteUpdate {nfa : NFA} (i : Fin nfa.nodes.size) : Prop :=
  match nfa[i] with
  | .done | .char _ _ | .sparse _ _ => True
  | _ => False

end Regex.VM
