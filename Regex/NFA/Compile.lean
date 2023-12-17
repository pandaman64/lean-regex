import Regex.Regex
import Regex.NFA.Basic

namespace NFA

def addNode (nodes : Array Node) (node : Node) : Array Node × Nat :=
  let nodes := nodes.push node
  (nodes, nodes.size - 1)

/--
  Thompson construction algorithm for converting the given regex to NFA.
-/
def compileRaw (r : Regex) : Array Node × Nat :=
  loop #[.done] 0 r
where
  /--
    The main loop of the compilation.

    It compiles the regex `r` into the given `nodes`. The compiled nodes transition to `next`
    if the input matches. It returns the new `nodes` and the corresponding ID for `r` in the array.
  -/
  loop (nodes : Array Node) (next : Nat) : Regex → Array Node × Nat
  | .empty => addNode nodes .fail
  | .epsilon => addNode nodes (.epsilon next)
  | .char c => addNode nodes (.char c next)
  | .alternate r₁ r₂ =>
    let (nodes, target₁) := loop nodes next r₁
    let (nodes, target₂) := loop nodes next r₂
    addNode nodes (.split target₁ target₂)
  | .concat r₁ r₂ =>
    let (nodes, next) := loop nodes next r₂
    loop nodes next r₁
  | .star r =>
    -- We need to generate a placeholder node first. We use `done` for it to save an allocation.
    -- TODO: check generated code
    let (nodes, start) := addNode nodes .done
    let (nodes, target) := loop nodes start r
    -- Patch the placeholder node
    -- TODO: prove in-bounds? It might be sufficient to use setD.
    let nodes := nodes.set! start (.split target next)
    (nodes, start)

#eval compileRaw (Regex.star (Regex.char 'a'))
#eval compileRaw (Regex.alternate (Regex.char 'a') (Regex.star (Regex.concat (Regex.char 'a') (Regex.char 'b'))))
#eval compileRaw (Regex.alternate Regex.empty (Regex.concat (Regex.char 'a') Regex.empty))

end NFA
