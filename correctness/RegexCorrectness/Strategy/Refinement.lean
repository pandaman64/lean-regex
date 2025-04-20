import Regex.Strategy
import RegexCorrectness.Strategy.Materialize

set_option autoImplicit false

open String (Pos)

namespace Regex.Strategy

variable {nfa : NFA} {bufferSize : Nat} {matched' : Option (List (Nat × Pos))} {matched : Option (Buffer bufferSize)}

def refineUpdate (update : List (Nat × Pos)) (buffer : Buffer bufferSize) : Prop :=
  materializeUpdates bufferSize update = buffer

@[simp]
theorem refineUpdate.empty {bufferSize : Nat} : refineUpdate HistoryStrategy.empty (BufferStrategy bufferSize).empty := rfl

def refineUpdateOpt : Option (List (Nat × Pos)) → Option (Buffer bufferSize) → Prop
  | .none, .none => True
  | .some update, .some buffer => refineUpdate update buffer
  | _, _ => False

theorem refineUpdateOpt.isSome_iff (h : refineUpdateOpt matched' matched) :
  matched'.isSome ↔ matched.isSome := by
  match matched', matched with
  | .none, .none => simp
  | .some _, .some _ => simp
  | .none, .some _ | .some _, .none => simp [refineUpdateOpt] at h

theorem refineUpdateOpt.isNone_iff (h : refineUpdateOpt matched' matched) :
  matched'.isNone ↔ matched.isNone := by
  match matched', matched with
  | .none, .none => simp
  | .some _, .some _ => simp
  | .none, .some _ | .some _, .none => simp [refineUpdateOpt] at h

theorem refineUpdateOpt.orElse {update₁ update₂ : Option (List (Nat × Pos))} {buffer₁ buffer₂ : Option (Buffer bufferSize)}
  (h₁ : refineUpdateOpt update₁ buffer₁) (h₂ : refineUpdateOpt update₂ buffer₂) :
  refineUpdateOpt (update₁ <|> update₂) (buffer₁ <|> buffer₂) := by
  match update₁, buffer₁ with
  | .some _, .some _ => simp [h₁]
  | .none, .none => simp [h₂]
  | .none, .some _ | .some _, .none => simp [refineUpdateOpt] at h₁

def refineUpdates (updates : Vector (List (Nat × Pos)) nfa.nodes.size) (buffers : Vector (Buffer bufferSize) nfa.nodes.size) : Prop :=
  ∀ (i : Fin nfa.nodes.size), refineUpdate updates[i] buffers[i]

end Regex.Strategy
