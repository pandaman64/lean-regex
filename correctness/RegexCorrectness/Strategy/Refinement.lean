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

theorem refineUpdateOpt.none_iff (h : refineUpdateOpt matched' matched) :
  (matched' = .none) ↔ (matched = .none) := by
  match matched', matched with
  | .none, .none => simp
  | .some _, .some _ => simp
  | .none, .some _ | .some _, .none => simp [refineUpdateOpt] at h

theorem refineUpdateOpt.or {update₁ update₂ : Option (List (Nat × Pos))} {buffer₁ buffer₂ : Option (Buffer bufferSize)}
  (h₁ : refineUpdateOpt update₁ buffer₁) (h₂ : refineUpdateOpt update₂ buffer₂) :
  refineUpdateOpt (Option.or update₁ update₂) (Option.or buffer₁ buffer₂) := by
  match update₁, buffer₁ with
  | .some _, .some _ => simp [h₁]
  | .none, .none => simp [h₂]
  | .none, .some _ | .some _, .none => simp [refineUpdateOpt] at h₁

theorem refineUpdateOpt.orElse {update₁ update₂ : Option (List (Nat × Pos))} {buffer₁ buffer₂ : Option (Buffer bufferSize)}
  (h₁ : refineUpdateOpt update₁ buffer₁) (h₂ : refineUpdateOpt update₂ buffer₂) :
  refineUpdateOpt (update₁ <|> update₂) (buffer₁ <|> buffer₂) := by
  simpa using refineUpdateOpt.or h₁ h₂

def refineUpdates (updates : Vector (List (Nat × Pos)) nfa.nodes.size) (buffers : Vector (Buffer bufferSize) nfa.nodes.size) : Prop :=
  ∀ (i : Fin nfa.nodes.size), refineUpdate updates[i] buffers[i]

theorem refineUpdates.set_set {updates : Vector (List (Nat × Pos)) nfa.nodes.size} {buffers : Vector (Buffer bufferSize) nfa.nodes.size}
  {i : Fin nfa.nodes.size} {update : List (Nat × Pos)} {buffer : Buffer bufferSize}
  (h₁ : refineUpdates updates buffers) (h₂ : refineUpdate update buffer) :
  refineUpdates (updates.set i update) (buffers.set i buffer) := by
  intro j
  if h : i.val = j.val then
    simpa [h] using h₂
  else
    simpa [h] using h₁ j

end Regex.Strategy
