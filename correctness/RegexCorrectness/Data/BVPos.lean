import Regex.Data.BVPos
import RegexCorrectness.Data.String

set_option autoImplicit false

open String (ValidPos Pos)

namespace Regex.Data.BVPos

variable {s : String} {startPos : ValidPos s}

@[ext]
theorem ext_index {p₁ p₂ : BVPos startPos} (h₂ : p₁.index = p₂.index) : p₁ = p₂ := by
  simp only [index, Pos.Raw.byteDistance, Fin.mk.injEq] at h₂
  simp only [BVPos.ext_iff, ValidPos.ext_iff, Pos.Raw.ext_iff]
  have : startPos.offset.byteIdx ≤ p₁.current.offset.byteIdx := p₁.le
  have : startPos.offset.byteIdx ≤ p₂.current.offset.byteIdx := p₂.le
  grind

def Splits (p : BVPos startPos) (l r : String) : Prop :=
  p.current.Splits l r

end Regex.Data.BVPos
