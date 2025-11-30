import Regex.Data.String

set_option autoImplicit false

open String (ValidPos)

namespace Regex.Data

/--
A valid position in a string with a lower bound.
-/
@[ext]
structure BVPos {s : String} (startPos : ValidPos s) where
  current : ValidPos s
  le : startPos ≤ current
deriving DecidableEq

def _root_.String.endBVPos (s : String) (startPos : ValidPos s) : BVPos startPos :=
  ⟨s.endValidPos, startPos.isValid.le_rawEndPos⟩

namespace BVPos

variable {s : String} {startPos : ValidPos s}

def refl {s : String} (startPos : ValidPos s) : BVPos startPos :=
  ⟨startPos, ValidPos.le_refl _⟩

def index (bp : BVPos startPos) : Fin (startPos.remainingBytes + 1) :=
  have lt : startPos.offset.byteDistance bp.current.offset < startPos.remainingBytes + 1 := by
    simp only [String.Pos.Raw.byteDistance, ValidPos.remainingBytes_eq]
    have : bp.current.offset.byteIdx ≤ s.utf8ByteSize := bp.current.isValid.le_rawEndPos
    grind
  ⟨startPos.offset.byteDistance bp.current.offset, lt⟩

theorem ne_iff_current_ne {bp₁ bp₂ : BVPos startPos} : bp₁ ≠ bp₂ ↔ bp₁.current ≠ bp₂.current := by
  grind [BVPos.ext]

theorem ne_end_iff_current_ne_end {bp : BVPos startPos} : bp ≠ s.endBVPos startPos ↔ bp.current ≠ s.endValidPos := by
  simp [ne_iff_current_ne, String.endBVPos]

def next (bp : BVPos startPos) (h : bp ≠ s.endBVPos startPos) : BVPos startPos :=
  let current' := bp.current.next (ne_end_iff_current_ne_end.mp h)
  have le' : startPos ≤ current' := ValidPos.le_of_lt (Nat.lt_of_le_of_lt bp.le bp.current.lt_next)
  ⟨current', le'⟩

def nextn (bp : BVPos startPos) (n : Nat) : BVPos startPos :=
  match n with
  | 0 => bp
  | n + 1 =>
    if h : bp ≠ s.endBVPos startPos then
      nextn (bp.next h) n
    else
      bp

def get (bp : BVPos startPos) (h : bp ≠ s.endBVPos startPos) : Char :=
  bp.current.get (ne_end_iff_current_ne_end.mp h)

def lt (bp₁ bp₂ : BVPos startPos) : Prop := bp₁.current < bp₂.current

instance : LT (BVPos startPos) := ⟨lt⟩

@[simp]
theorem lt_next {bp : BVPos startPos} (h : bp ≠ s.endBVPos startPos) : bp < bp.next h :=
  bp.current.lt_next (h := ne_end_iff_current_ne_end.mp h)

theorem wellFounded_gt : WellFounded (fun (p : BVPos startPos) q => q < p) :=
  InvImage.wf BVPos.current ValidPos.wellFounded_gt

instance : WellFoundedRelation (BVPos startPos) where
  rel p q := q < p
  wf := wellFounded_gt

end BVPos

end Regex.Data

-- From Init.Data.String.Termination
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  (with_reducible change (_ : Regex.Data.BVPos _) < _
   simp) <;> done)
