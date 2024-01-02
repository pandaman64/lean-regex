import Regex.NFA.VM.Basic
import Regex.NFA.Transition

namespace NFA.VM

def NodeSet.toSet (ns : NodeSet n) : Set Nat := { i | ∃ h : i < n, ns.get ⟨i, h⟩ }

end NFA.VM
