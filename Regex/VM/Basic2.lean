import Regex.Data.Array
import Regex.Data.SparseSet
import Regex.NFA.Basic

set_option autoImplicit false

open Regex.Data (SparseSet Vec)
open Regex (NFA)
open String (Pos)

namespace Regex.VM

-- `nfa.maxTag` is erased, so we don't need to traverse the whole nodes to use `Buffer`.
def Buffer (nfa : NFA) := Vec (Option Pos) (nfa.maxTag + 1)

/--
The stack for εClosure. Each entry consists of a pair of an NFA state and the capture group buffer
at that state.
-/
abbrev εStack (nfa : NFA) := List (Buffer nfa × Fin nfa.nodes.size)

-- TODO: System V ABI only supports at most 6 arguments in registers. Should we put `wf` as `Subtype` to reduce the number of arguments?
-- TODO: Windows even supports only 4 arguments in registers.
def εClosure2 (nfa : NFA) (wf : nfa.WellFormed) (pos : Pos)
  (next : SparseSet nfa.nodes.size) (matched : Option (Buffer nfa)) (buffers : Vec (Buffer nfa) nfa.nodes.size)
  (stack : εStack nfa) :
  (SparseSet nfa.nodes.size × Option (Buffer nfa) × Vec (Buffer nfa) nfa.nodes.size) :=
  match stack with
  | [] => (next, matched, buffers)
  | (buffer, state) :: stack' =>
    if state ∈ next then
      εClosure2 nfa wf pos next matched buffers stack'
    else
      let next' := next.insert state
      match hn : nfa[state] with
      | .epsilon state' =>
        have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
        εClosure2 nfa wf pos next' matched buffers ((buffer, ⟨state', isLt⟩) :: stack')
      | .split state₁ state₂ =>
        have isLt : state₁ < nfa.nodes.size ∧ state₂ < nfa.nodes.size := wf.inBounds' state hn
        εClosure2 nfa wf pos next' matched buffers ((buffer, ⟨state₁, isLt.1⟩) :: (buffer, ⟨state₂, isLt.2⟩):: stack')
      | .save offset state' =>
        have isLt : state' < nfa.nodes.size := wf.inBounds' state hn
        have offsetLe := nfa.le_maxTag state hn
        let buffer' := buffer.set offset (by omega) pos
        εClosure2 nfa wf pos next' matched buffers ((buffer', ⟨state', isLt⟩) :: stack')
      | .done =>
        let matched' := matched <|> buffer
        let buffers' := buffers.set state state.isLt buffer
        εClosure2 nfa wf pos next' matched' buffers' stack'
      | .char _ _ =>
        let buffers' := buffers.set state state.isLt buffer
        εClosure2 nfa wf pos next' matched buffers' stack'
      | .sparse _ _ =>
        let buffers' := buffers.set state state.isLt buffer
        εClosure2 nfa wf pos next' matched buffers' stack'
      | .fail => εClosure2 nfa wf pos next' matched buffers stack'
termination_by (next.measure, stack)

-- TODO: redeclare a bit simplifed version of function induction
#check εClosure2.induct

end Regex.VM
