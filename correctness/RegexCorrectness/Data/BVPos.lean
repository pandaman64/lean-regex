module

import all Regex.Data.BVPos
public import Regex.Data.BVPos
import RegexCorrectness.Data.String

open String (Pos)

public section

namespace Regex.Data.BVPos

variable {s : String} {startPos : Pos s}

@[simp]
theorem index_eq_of_le {p : Pos s} (le le' : startPos ≤ p) :
    BVPos.index (⟨p, le⟩ : BVPos startPos) = BVPos.index (⟨p, le'⟩ : BVPos startPos) := by
  ext
  simp [BVPos.index]

@[ext]
theorem ext_index {p₁ p₂ : BVPos startPos} (h₂ : p₁.index = p₂.index) : p₁ = p₂ := by
  simp only [index, Pos.Raw.byteDistance, Fin.mk.injEq] at h₂
  simp only [BVPos.ext_iff, Pos.ext_iff, Pos.Raw.ext_iff]
  have : startPos.offset.byteIdx ≤ p₁.current.offset.byteIdx := p₁.le
  have : startPos.offset.byteIdx ≤ p₂.current.offset.byteIdx := p₂.le
  grind

@[simp]
theorem get_eq_get (pos : BVPos startPos) (h : pos ≠ s.endBVPos startPos) :
    pos.get h = pos.current.get (Regex.Data.BVPos.ne_end_iff_current_ne_end.mp h) := by
  grind [Regex.Data.BVPos.get]

def Splits (p : BVPos startPos) (l r : String) : Prop :=
  p.current.Splits l r

end Regex.Data.BVPos

end
