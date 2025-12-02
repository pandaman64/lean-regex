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

-- def Valid (bit : BVPos startIdx maxIdx) : Prop := bit.it.Valid

-- theorem next_valid {bit : BVPos startIdx maxIdx} (h : bit.hasNext) (v : bit.Valid) : (bit.next h).Valid :=
--   String.Iterator.Valid.next v h

-- @[simp]
-- theorem toEnd_toString (bit : BVPos startIdx maxIdx) : bit.toEnd.toString = bit.toString := by
--   simp [toEnd, Iterator.toEnd, toString]

-- theorem toEnd_pos (bit : BVPos startIdx maxIdx) : bit.toEnd.pos = bit.toString.endPos := by
--   simp [toEnd, Iterator.toEnd, toString, pos]

-- theorem toEnd_valid (bit : BVPos startIdx maxIdx) : bit.toEnd.Valid := String.Iterator.Valid.toEnd bit.it

-- theorem pos_le_toEnd_pos (bit : BVPos startIdx maxIdx) : bit.pos ≤ bit.toEnd.pos := by
--   simp [toEnd, Iterator.toEnd, pos]
--   show bit.it.pos.byteIdx ≤ bit.toString.endPos.byteIdx
--   exact bit.eq ▸ bit.le

-- theorem toEnd_not_hasNext (bit : BVPos startIdx maxIdx) : ¬bit.toEnd.hasNext := by
--   intro hnext
--   simp [hasNext, Iterator.hasNext, toEnd, Iterator.toEnd] at hnext

-- @[simp]
-- theorem next_toEnd {bit : BVPos startIdx maxIdx} (h : bit.hasNext) : (bit.next h).toEnd = bit.toEnd := by
--   simp [toEnd, Iterator.toEnd, next, Iterator.next']

-- theorem nextn_valid {bit : BVPos startIdx maxIdx} {n : Nat} (v : bit.Valid) : (bit.nextn n).Valid := by
--   induction n generalizing bit with
--   | zero => simpa [nextn] using v
--   | succ n ih =>
--     if h : bit.hasNext then
--       simp [nextn, h]
--       exact ih (bit.next_valid h v)
--     else
--       simpa [nextn, h] using v

-- theorem next_nextn {bit : BVPos startIdx maxIdx} {n : Nat} (hnext : bit.hasNext) : (bit.next hnext).nextn n = bit.nextn (n + 1) := by
--   cases n with
--   | zero => simp [nextn, hnext]
--   | succ n => simp [nextn, hnext]

-- theorem byteIdx_le_nextn_byteIdx (bit : BVPos startIdx maxIdx) (n : Nat) : bit.pos.byteIdx ≤ (bit.nextn n).pos.byteIdx := by
--   induction n generalizing bit with
--   | zero => simp [nextn]
--   | succ n ih =>
--     simp [nextn]
--     if h : bit.hasNext then
--       simp [h]
--       exact Nat.le_of_lt (Nat.lt_of_lt_of_le (byteIdx_lt_next_byteIdx h) (ih (bit.next h)))
--     else
--       simp [h]

-- theorem nextn_toString {bit : BVPos startIdx maxIdx} {n : Nat} : (bit.nextn n).toString = bit.toString := by
--   induction n generalizing bit with
--   | zero => simp [nextn]
--   | succ n ih =>
--     if h : bit.hasNext then
--       simp [nextn, h, ih, next_toString]
--     else
--       simp [nextn, h]

-- theorem hasNext_of_nextn_hasNext {bit : BVPos startIdx maxIdx} {n : Nat} (hnext : (bit.nextn n).hasNext) : bit.hasNext := by
--   have le : bit.pos.byteIdx ≤ (bit.nextn n).pos.byteIdx := bit.byteIdx_le_nextn_byteIdx n
--   have lt : (bit.nextn n).pos.byteIdx < bit.toString.endPos.byteIdx := by
--     have : (bit.nextn n).pos.byteIdx < (bit.nextn n).toString.endPos.byteIdx := by
--       simp [hasNext, Iterator.hasNext] at hnext
--       exact hnext
--     simpa [nextn_toString]
--   show decide (bit.pos.byteIdx < bit.toString.endPos.byteIdx) = true
--   simp only [decide_eq_true_eq]
--   grind

-- theorem nextn_next_eq_next_nextn {bit : BVPos startIdx maxIdx} {n : Nat} (hnext : (bit.nextn n).hasNext) : (bit.nextn n).next hnext = (bit.next (hasNext_of_nextn_hasNext hnext)).nextn n := by
--   induction n generalizing bit with
--   | zero => simp [nextn]
--   | succ n ih =>
--     have hnext₀ : bit.hasNext := hasNext_of_nextn_hasNext hnext
--     simp [nextn, hnext₀] at hnext
--     have hnext₁ : (bit.next hnext₀).hasNext := hasNext_of_nextn_hasNext hnext
--     simp [nextn, hnext₀, hnext₁]
--     exact ih hnext

-- theorem nextn_next {bit : BVPos startIdx maxIdx} {n : Nat} (hnext : (bit.nextn n).hasNext) : (bit.nextn n).next hnext = bit.nextn (n + 1) := by
--   rw [nextn_next_eq_next_nextn hnext, next_nextn]

-- theorem nextn_not_hasNext {bit : BVPos startIdx maxIdx} {n : Nat} (hnext : ¬bit.hasNext) : (bit.nextn n) = bit := by
--   cases n with
--   | zero => simp [nextn]
--   | succ n => simp [nextn, hnext]

-- theorem nextn_add (bit : BVPos startIdx maxIdx) (n₁ n₂ : Nat) : bit.nextn (n₁ + n₂) = (bit.nextn n₁).nextn n₂ := by
--   induction n₁ generalizing bit with
--   | zero => simp [nextn]
--   | succ n₁ ih =>
--     have : n₁ + 1 + n₂ = (n₁ + n₂) + 1 := by omega
--     if hnext : bit.hasNext then
--       simpa [nextn, this, hnext] using ih (bit.next hnext)
--     else
--       simp [nextn, this, hnext, nextn_not_hasNext hnext]

-- def ValidFor (l r : List Char) (bit : BVPos startIdx maxIdx) : Prop := bit.it.ValidFor l r

-- namespace ValidFor

-- theorem hasNext {l r} {bit : BVPos startIdx maxIdx} (vf : ValidFor l r bit) : bit.hasNext ↔ r ≠ [] := by
--   unfold ValidFor at vf
--   exact vf.hasNext

-- theorem next {l c r} {bit : BVPos startIdx maxIdx} (vf : ValidFor l (c :: r) bit) : ValidFor (c :: l) r (bit.next (by simp [vf.hasNext])) := by
--   unfold ValidFor at vf
--   exact vf.next

-- theorem next' {l r} {bit : BVPos startIdx maxIdx} (h : bit.hasNext) (vf : ValidFor l r bit) : ∃ c r', r = c :: r' ∧ ValidFor (c :: l) r' (bit.next h) := by
--   match r with
--   | [] => simp [vf.hasNext] at h
--   | c :: r' => exact ⟨c, r', rfl, vf.next⟩

-- theorem curr {l c r} {bit : BVPos startIdx maxIdx} (vf : ValidFor l (c :: r) bit) : bit.curr (by simp [vf.hasNext]) = c := by
--   simp [BVPos.curr, bit.it.curr'_eq_curr, String.Iterator.ValidFor.curr vf]

-- theorem toString {l r} {bit : BVPos startIdx maxIdx} (vf : ValidFor l r bit) : bit.toString = String.mk (l.reverse ++ r) := by
--   simp [ValidFor] at vf
--   simpa [toString] using vf.toString

-- theorem pos {l r} {bit : BVPos startIdx maxIdx} (vf : ValidFor l r bit) : bit.pos = ⟨String.utf8Len l⟩ := by
--   simp [ValidFor] at vf
--   simpa [pos] using vf.pos

-- theorem valid {l r} {bit : BVPos startIdx maxIdx} (vf : ValidFor l r bit) : bit.Valid := by
--   simp [ValidFor] at vf
--   exact vf.valid

-- theorem eq {l l' r r'} {bit : BVPos startIdx maxIdx} (vf : ValidFor l r bit) (vf' : ValidFor l' r' bit) : l = l' ∧ r = r' :=
--   Iterator.ValidFor.eq vf vf'

-- theorem eq_it {l r} {bit bit' : BVPos startIdx maxIdx} (vf : ValidFor l r bit) (vf' : ValidFor l r bit') : bit = bit' :=
--   BVPos.ext (Iterator.ValidFor.eq_it vf vf')

-- end ValidFor

-- namespace Valid

-- theorem validFor {bit : BVPos startIdx maxIdx} (v : bit.Valid) : ∃ l r, ValidFor l r bit := by
--   simp [Valid] at v
--   exact v.validFor

-- theorem validFor_of_hasNext {bit : BVPos startIdx maxIdx} (h : bit.hasNext) (v : bit.Valid) :
--   ∃ l r, ValidFor l (bit.curr h :: r) bit := by
--   have ⟨l, r, vf⟩ := validFor v
--   match h' : r with
--   | [] => simp [vf.hasNext] at h
--   | c :: r' => exact ⟨l, r', by simpa [vf.curr] using vf⟩

-- theorem next {bit : BVPos startIdx maxIdx} (hnext : bit.hasNext) (v : bit.Valid) : (bit.next hnext).Valid := by
-- have ⟨l, r, vf⟩ := v.validFor_of_hasNext hnext
-- exact vf.next.valid

-- end Valid

-- theorem toEnd_validFor (bit : BVPos startIdx maxIdx) : ValidFor bit.toString.data.reverse [] bit.toEnd := by
--   have ⟨l, r, vf⟩ := bit.toEnd_valid.validFor
--   have eqr := vf.hasNext.not.mp bit.toEnd_not_hasNext
--   simp at eqr
--   rw [eqr] at vf
--   have eq := bit.toEnd_toString ▸ vf.toString
--   simpa [eq] using vf

-- theorem eq_of_valid_of_next_eq {bit bit' : BVPos startIdx maxIdx} (v : bit.Valid) (v' : bit'.Valid) (hnext : bit.hasNext) (hnext' : bit'.hasNext) (eq : bit.next hnext = bit'.next hnext') : bit = bit' := by
--   have ⟨l, r, vf⟩ := v.validFor_of_hasNext hnext
--   have vfn := vf.next
--   have ⟨l', r', vf'⟩ := v'.validFor_of_hasNext hnext'
--   have vfn' := vf'.next

--   have eqs : bit.curr hnext :: l = bit'.curr hnext' :: l' ∧ r = r' := vfn.eq (eq ▸ vfn')
--   simp at eqs
--   simp [eqs] at vf

--   exact vf.eq_it vf'

-- inductive Reaches : BVPos startIdx maxIdx → BVPos startIdx maxIdx → Prop
-- | refl {bit} (v : bit.Valid) : Reaches bit bit
-- | next {bit₁ bit₂ : BVPos startIdx maxIdx} (v : bit₁.Valid) (hnext : bit₁.hasNext) (rest : (bit₁.next hnext).Reaches bit₂) : Reaches bit₁ bit₂

-- namespace Reaches

-- variable {bit₁ bit₂ : BVPos startIdx maxIdx}

-- theorem trans {bit₁ bit₂ bit₃ : BVPos startIdx maxIdx} (h₁ : Reaches bit₁ bit₂) (h₂ : Reaches bit₂ bit₃) : Reaches bit₁ bit₃ := by
--   induction h₁ with
--   | refl v => exact h₂
--   | next v hnext rest ih => exact .next v hnext (ih h₂)

-- theorem validL (h : Reaches bit₁ bit₂) : bit₁.Valid := by
--   cases h with
--   | refl v => exact v
--   | next v _ _ => exact v

-- theorem validR (h : Reaches bit₁ bit₂) : bit₂.Valid := by
--   induction h with
--   | refl v => exact v
--   | next _ _ _ ih => exact ih

-- theorem toString (h : Reaches bit₁ bit₂) : bit₂.toString = bit₁.toString := by
--   induction h with
--   | refl v => rfl
--   | next v _ _ ih => simp [next_toString, ih]

-- theorem le_pos (h : Reaches bit₁ bit₂) : bit₁.pos ≤ bit₂.pos := by
--   induction h with
--   | refl v => exact Nat.le_refl _
--   | next _ hnext _ ih => exact Nat.le_of_lt (Nat.lt_of_lt_of_le (byteIdx_lt_next_byteIdx hnext) ih)

-- theorem next' (hnext₂ : bit₂.hasNext) (h : Reaches bit₁ bit₂) : Reaches bit₁ (bit₂.next hnext₂) := by
--   induction h with
--   | refl v => exact .next v hnext₂ (.refl (v.next hnext₂))
--   | @next bit₁ bit₂ v hnext₁ _ ih => exact .next v hnext₁ (ih hnext₂)

-- theorem next'_iff' {bit₂'} (v₂ : bit₂.Valid) (hnext₂ : bit₂.hasNext) (eq : bit₂.next hnext₂ = bit₂') : Reaches bit₁ bit₂' ↔ Reaches bit₁ bit₂ ∨ (bit₁.Valid ∧ bit₁ = bit₂') := by
--   apply Iff.intro
--   . intro h
--     induction h with
--     | refl v => exact .inr ⟨v, rfl⟩
--     | @next bit₁ bit₂' v₁ hnext₁ rest ih =>
--       match ih eq with
--       | .inl h => exact .inl (.next v₁ hnext₁ h)
--       | .inr ⟨v', eq'⟩ =>
--         have eq₁₂ : bit₁ = bit₂ := eq_of_valid_of_next_eq v₁ v₂ hnext₁ hnext₂ (eq ▸ eq')
--         exact .inl (eq₁₂ ▸ .refl v₁)
--   . intro h
--     match h with
--     | .inl h => exact eq ▸ h.next' hnext₂
--     | .inr ⟨v, eq⟩ => exact eq ▸ .refl v

-- @[simp]
-- theorem next'_iff (v₂ : bit₂.Valid) (hnext₂ : bit₂.hasNext) : Reaches bit₁ (bit₂.next hnext₂) ↔ Reaches bit₁ bit₂ ∨ (bit₁.Valid ∧ bit₁ = bit₂.next hnext₂) :=
--   next'_iff' v₂ hnext₂ rfl

-- theorem of_validFor {l m r : List Char} (vf₁ : ValidFor l.reverse (m ++ r) bit₁) (vf₂ : ValidFor (m.reverse ++ l.reverse) r bit₂) : Reaches bit₁ bit₂ := by
--   induction m generalizing l bit₁ with
--   | nil =>
--     simp at vf₁ vf₂
--     have eq := vf₁.eq_it vf₂
--     exact eq ▸ .refl vf₁.valid
--   | cons c m ih =>
--     have hnext₁ := vf₁.hasNext
--     simp at hnext₁

--     have vf₁' := vf₁.next
--     simp at vf₁' vf₂
--     have h : (bit₁.next hnext₁).Reaches bit₂ := ih (l := l ++ [c]) (bit₁ := bit₁.next hnext₁) (by simpa using vf₁') (by simpa using vf₂)
--     exact .next vf₁.valid hnext₁ h

-- theorem validFor (h : Reaches bit₁ bit₂) : ∃ (l m r : List Char), ValidFor l.reverse (m ++ r) bit₁ ∧ ValidFor (m.reverse ++ l.reverse) r bit₂ :=
--   String.Iterator.Valid.validFor_of_valid_pos_le h.validL h.validR h.toString.symm h.le_pos

-- theorem iff_validFor : Reaches bit₁ bit₂ ↔ ∃ (l m r : List Char), ValidFor l.reverse (m ++ r) bit₁ ∧ ValidFor (m.reverse ++ l.reverse) r bit₂ :=
--   ⟨validFor, fun ⟨l, m, r, vf₁, vf₂⟩ => of_validFor (l := l) (m := m) (r := r) vf₁ vf₂⟩

-- theorem iff_valid_le_pos : Reaches bit₁ bit₂ ↔ bit₁.Valid ∧ bit₂.Valid ∧ bit₁.toString = bit₂.toString ∧ bit₁.pos ≤ bit₂.pos := by
--   apply Iff.intro
--   . intro h
--     have ⟨l, m, r, vf₁, vf₂⟩ := h.validFor
--     exact ⟨vf₁.valid, vf₂.valid, by simp [vf₁.toString, vf₂.toString] , by simp [vf₁.pos, vf₂.pos]⟩
--   . intro ⟨v₁, v₂, eq, le⟩
--     have ⟨l, m, r, vf₁, vf₂⟩ := Iterator.Valid.validFor_of_valid_pos_le v₁ v₂ eq le
--     exact of_validFor (l := l) (m := m) (r := r) vf₁ vf₂

-- theorem _root_.Regex.Data.BVPos.reaches_toEnd {bit : BVPos startIdx maxIdx} (v : bit.Valid) : bit.Reaches bit.toEnd := by
--   have ⟨lrev, m, vf⟩ := v.validFor
--   rw [Reaches.iff_validFor]
--   exact ⟨lrev.reverse, m, [], by simpa using vf, by simpa [vf.toString] using bit.toEnd_validFor⟩

-- theorem reaches_toEnd_of_reaches (h : bit₁.Reaches bit₂) : bit₂.Reaches bit₁.toEnd := by
--   induction h with
--   | @refl bit v => exact bit.reaches_toEnd v
--   | @next bit₁ bit₂ _ _ _ ih => simpa using ih

-- end Reaches

-- def BetweenI (bit bs be : BVPos startIdx maxIdx) : Prop := bs.Reaches bit ∧ bit.Reaches be

-- def BetweenE (bit bs be : BVPos startIdx maxIdx) : Prop := bit.pos < be.pos ∧ bit.BetweenI bs be

-- namespace BetweenI

-- variable {bit bs be : BVPos startIdx maxIdx}

-- theorem reachesSE (h : bit.BetweenI bs be) : bs.Reaches be := h.1.trans h.2

-- theorem le_pos (h : bit.BetweenI bs be) : bit.pos ≤ be.pos := h.2.le_pos

-- @[simp]
-- theorem next_iff (v : be.Valid) (hnext : be.hasNext) : bit.BetweenI bs (be.next hnext) ↔ bit.BetweenI bs be ∨ (bs.Reaches bit ∧ bit = be.next hnext) := by
--   simp [BetweenI, v, ←and_or_left]
--   intro h
--   simp [h.validR]

-- theorem iffE : bit.BetweenI bs be ↔ bit.BetweenE bs be ∨ (bs.Reaches bit ∧ bit = be) := by
--   apply Iff.intro
--   . intro h
--     if lt : bit.pos < be.pos then
--       exact .inl ⟨lt, h⟩
--     else
--       have eq_pos : bit.pos = be.pos := by
--         simp [String.Pos.Raw.ext_iff]
--         exact Nat.le_antisymm (le_pos h) (Nat.le_of_not_lt lt)
--       have eq : bit = be := by
--         simp [BVPos.ext_pos_iff, eq_pos, h.2.toString]
--       exact .inr ⟨h.1, eq⟩
--   . intro h
--     match h with
--     | .inl ⟨lt, h⟩ => exact h
--     | .inr ⟨h, eq⟩ => exact ⟨h, eq ▸ .refl h.validR⟩

-- end BetweenI

-- namespace BetweenE

-- variable {bit bs be : BVPos startIdx maxIdx}

-- theorem validE (h : bit.BetweenE bs be) : be.Valid := h.2.2.validR

-- theorem ne_end (h : bit.BetweenE bs be) : bit ≠ be := by
--   intro eq
--   have lt : bit.pos < be.pos := h.1
--   simp only [eq, String.Pos.Raw.lt_iff, Nat.lt_irrefl] at lt

-- theorem next_iffI (v : be.Valid) (hnext : be.hasNext) : bit.BetweenE bs (be.next hnext) ↔ bit.BetweenI bs be := by
--   simp [BetweenE, v]
--   apply Iff.intro
--   . intro ⟨lt, h⟩
--     match h with
--     | .inl h => exact h
--     | .inr ⟨_, eq⟩ => simp only [eq, String.Pos.Raw.lt_iff, Nat.lt_irrefl] at lt
--   . intro h
--     exact ⟨Nat.lt_of_le_of_lt (h.le_pos) (pos_lt_next_pos hnext), .inl h⟩

-- @[simp]
-- theorem next_iff (v : be.Valid) (hnext : be.hasNext) : bit.BetweenE bs (be.next hnext) ↔ bit.BetweenE bs be ∨ (bs.Reaches bit ∧ bit = be) := by
--   simp [next_iffI v hnext, BetweenI.iffE]

-- @[simp]
-- theorem not_self {bit₁ bit₂ : BVPos startIdx maxIdx} : ¬bit₁.BetweenE bit₂ bit₂ := by
--   intro ⟨lt, h⟩
--   exact Nat.not_lt_of_le (h.1.le_pos) lt

-- end BetweenE

-- end Regex.Data.BVPos
