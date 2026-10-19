module

public import Regex.VM.FlatBuffer.Basic

/-!
Row-copy and row-fill proofs. The walks themselves live in `FlatBuffer.Basic`.
-/

public section

namespace Regex.VM.FlatBuffer

open String (Pos PosPlusOne)
open Regex.VM.Wide (toNat_toUSize_of_lt_2_pow_32)

private theorem copySlots_size (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size) :
    (copySlots dst src nSlots hDstFit hSrcFit k hk a hDst hSrc).size = a.size := by
  unfold copySlots
  by_cases hk' : k = nSlots
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    apply Eq.trans
    · apply copySlots_size
    · apply uset_size
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact ({} : IndexStep nSlots k (rowMul8_le hSrcFit) hk hk').hMeasure

/-- Copying a row does not change the buffer length. -/
theorem copyRow_size (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32) :
    (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size = a.size := by
  unfold copyRow
  exact copySlots_size dst src nSlots hDstFit hSrcFit 0 (zero_le_toNat _) a hDst hSrc

/-- Stepping `k` preserves disjointness from the not-yet-written suffix. -/
private theorem suffixStepDisj (off base nSlots k : Nat)
    (hdisj : off + 8 ≤ base + k * 8 ∨ base + nSlots * 8 ≤ off) (hlt : k < nSlots) :
    (off + 8 ≤ base + k * 8 ∨ base + k * 8 + 8 ≤ off) ∧
      (off + 8 ≤ base + (k + 1) * 8 ∨ base + nSlots * 8 ≤ off) := by
  refine ⟨?_, ?_⟩
  · cases hdisj with
    | inl hle => exact Or.inl hle
    | inr hge =>
      right
      have : k + 1 ≤ nSlots := Nat.succ_le_of_lt hlt
      omega
  · cases hdisj with
    | inl hle =>
      left
      omega
    | inr hge => exact Or.inr hge

/-- A slot disjoint from the not-yet-copied suffix of the destination row is left unchanged. -/
private theorem copySlots_outside (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat + k.toNat * 8 ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat) :
    uget (copySlots dst src nSlots hDstFit hSrcFit k hk a hDst hSrc) off
        (by rw [copySlots_size dst src nSlots hDstFit hSrcFit k hk a hDst hSrc]; exact hoff) =
      uget a off hoff := by
  unfold copySlots
  by_cases hk' : k = nSlots
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    let step : IndexStep nSlots k (rowMul8_le hSrcFit) hk hk' := {}
    let srcOff := src + k * slotBytes
    let dstOff := dst + k * slotBytes
    have hSrcNat : srcOff.toNat = src.toNat + k.toNat * 8 :=
      slotAddr_toNat src k step.hMul (slotOff_lt step.hlt hSrcFit)
    have hDstNat : dstOff.toNat = dst.toNat + k.toNat * 8 :=
      slotAddr_toNat dst k step.hMul (slotOff_lt step.hlt hDstFit)
    have hRead : srcOff.toNat + 8 ≤ a.size := by rw [hSrcNat]; exact slotOff_le step.hlt hSrc
    have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le step.hlt hDst
    let a' := uset a dstOff (uget a srcOff hRead) hWrite
    have hpair := suffixStepDisj off.toNat dst.toNat nSlots.toNat k.toNat hdisj step.hlt
    have hWriteDisj : off.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + 8 ≤ off.toNat := by
      rw [hDstNat]
      exact hpair.1
    have hdisj' : off.toNat + 8 ≤ dst.toNat + (k + 1).toNat * 8 ∨
        dst.toNat + nSlots.toNat * 8 ≤ off.toNat := by
      rw [step.hNext]
      exact hpair.2
    have hRec := copySlots_outside dst src nSlots hDstFit hSrcFit (k + 1) step.hkNext
      a' (by rw [uset_size]; exact hDst) (by rw [uset_size]; exact hSrc)
      off (by rw [uset_size]; exact hoff) hdisj'
    have hKeep := uget_uset_disjoint a dstOff off (uget a srcOff hRead) hWrite hoff hWriteDisj
    exact (uget_irrel _ _ _ _).trans (hRec.trans hKeep)
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact ({} : IndexStep nSlots k (rowMul8_le hSrcFit) hk hk').hMeasure

/--
Slot `j` of the suffix still to be copied equals slot `j` of the source, when the two
windows are the same row or do not overlap.
-/
private theorem copySlots_uget (dst src nSlots : USize)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hsep : dst.toNat = src.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ src.toNat ∨
      src.toNat + nSlots.toNat * 8 ≤ dst.toNat)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (j : Nat) (hj : j < nSlots.toNat) (hkj : k.toNat ≤ j) :
    uget (copySlots dst src nSlots hDstFit hSrcFit k hk a hDst hSrc) ((dst.toNat + j * 8).toUSize)
      (by
        rw [copySlots_size dst src nSlots hDstFit hSrcFit k hk a hDst hSrc]
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hDstFit)]
        exact slotOff_le hj hDst) =
      uget a ((src.toNat + j * 8).toUSize) (by
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hSrcFit)]
        exact slotOff_le hj hSrc) := by
  unfold copySlots
  by_cases hk' : k = nSlots
  · have hkNat : k.toNat = nSlots.toNat := by rw [hk']
    omega
  · simp only [hk', ↓reduceDIte]
    let step : IndexStep nSlots k (rowMul8_le hSrcFit) hk hk' := {}
    let srcOff := src + k * slotBytes
    let dstOff := dst + k * slotBytes
    have hSrcNat : srcOff.toNat = src.toNat + k.toNat * 8 :=
      slotAddr_toNat src k step.hMul (slotOff_lt step.hlt hSrcFit)
    have hDstNat : dstOff.toNat = dst.toNat + k.toNat * 8 :=
      slotAddr_toNat dst k step.hMul (slotOff_lt step.hlt hDstFit)
    have hRead : srcOff.toNat + 8 ≤ a.size := by rw [hSrcNat]; exact slotOff_le step.hlt hSrc
    have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le step.hlt hDst
    let word := uget a srcOff hRead
    let a' := uset a dstOff word hWrite
    have hDst' : dst.toNat + nSlots.toNat * 8 ≤ a'.size := by rw [uset_size]; exact hDst
    have hSrc' : src.toNat + nSlots.toNat * 8 ≤ a'.size := by rw [uset_size]; exact hSrc
    by_cases hjk : j = k.toNat
    · have hTail : dstOff.toNat + 8 ≤ dst.toNat + (k + 1).toNat * 8 := by
        rw [hDstNat, step.hNext]
        omega
      have hOut := copySlots_outside dst src nSlots hDstFit hSrcFit (k + 1) step.hkNext
        a' hDst' hSrc' dstOff (by rw [uset_size]; exact hWrite) (Or.inl hTail)
      have hDstOff : dstOff = (dst.toNat + j * 8).toUSize := by
        apply USize.toNat_inj.mp
        rw [hDstNat, toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hDstFit), hjk]
      have hSrcOff : srcOff = (src.toNat + j * 8).toUSize := by
        apply USize.toNat_inj.mp
        rw [hSrcNat, toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hSrcFit), hjk]
      have hStep := hOut.trans (uget_uset a dstOff word hWrite)
      exact ((uget_congr (copySlots dst src nSlots hDstFit hSrcFit (k + 1) step.hkNext a' hDst' hSrc')
          dstOff ((dst.toNat + j * 8).toUSize) hDstOff _ _).symm).trans
        (hStep.trans (uget_congr a srcOff ((src.toNat + j * 8).toUSize) hSrcOff hRead _))
    · have hkj' : (k + 1).toNat ≤ j := by
        rw [step.hNext]
        omega
      have hRec := copySlots_uget dst src nSlots hDstFit hSrcFit hsep (k + 1) step.hkNext
        a' hDst' hSrc' j hj hkj'
      let srcSlot := (src.toNat + j * 8).toUSize
      have hSrcSlotNat : srcSlot.toNat = src.toNat + j * 8 :=
        toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hSrcFit)
      have hSrcSlot : srcSlot.toNat + 8 ≤ a.size := by
        rw [hSrcSlotNat]; exact slotOff_le hj hSrc
      have hSepSlots : srcSlot.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + 8 ≤ srcSlot.toNat := by
        rw [hSrcSlotNat, hDstNat]
        cases hsep with
        | inl heq =>
          right
          rw [heq]
          omega
        | inr hrest =>
          cases hrest with
          | inl hbefore =>
            right
            omega
          | inr hafter =>
            left
            omega
      have hStable := uget_uset_disjoint a dstOff srcSlot word hWrite hSrcSlot hSepSlots
      exact (uget_irrel _ _ _ _).trans (hRec.trans hStable)
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact ({} : IndexStep nSlots k (rowMul8_le hSrcFit) hk hk').hMeasure

/--
Destination slot `j` equals source slot `j` when the rows are the same or do not overlap.
-/
theorem copyRow_uget (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hsep : dst.toNat = src.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ src.toNat ∨
      src.toNat + nSlots.toNat * 8 ≤ dst.toNat)
    (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤
      (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size)
    (hSrcSlot : ((src.toNat + j * 8).toUSize).toNat + 8 ≤ a.size) :
    uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit) ((dst.toNat + j * 8).toUSize) hSlot =
      uget a ((src.toNat + j * 8).toUSize) hSrcSlot := by
  unfold copyRow
  exact (uget_irrel _ _ _ _).trans
    ((copySlots_uget dst src nSlots hDstFit hSrcFit hsep 0 (zero_le_toNat _) a hDst hSrc j hj
      (zero_le_toNat _)).trans (uget_irrel _ _ _ _))

/-- A slot that does not meet the destination row is unchanged. -/
theorem copyRow_uget_disjoint (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size) :
    uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit) off hSlot = uget a off hoff := by
  unfold copyRow
  exact (uget_irrel _ _ _ _).trans
    (copySlots_outside dst src nSlots hDstFit hSrcFit 0 (zero_le_toNat _) a hDst hSrc off hoff
      (by simpa [USize.toNat_zero] using hdisj))

private theorem fillSlots_size (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size) :
    (fillSlots dst nSlots v hFit k hk a hDst).size = a.size := by
  unfold fillSlots
  by_cases hk' : k = nSlots
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    apply Eq.trans
    · apply fillSlots_size
    · apply uset_size
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact ({} : IndexStep nSlots k (rowMul8_le hFit) hk hk').hMeasure

/-- Filling a row does not change the buffer length. -/
theorem fillRow_size (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32) :
    (fillRow a dst nSlots v hDst hFit).size = a.size := by
  unfold fillRow
  exact fillSlots_size dst nSlots v hFit 0 (zero_le_toNat _) a hDst

/-- A slot disjoint from the not-yet-written suffix of the row is left unchanged. -/
private theorem fillSlots_outside (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat + k.toNat * 8 ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat) :
    uget (fillSlots dst nSlots v hFit k hk a hDst) off
        (by rw [fillSlots_size dst nSlots v hFit k hk a hDst]; exact hoff) =
      uget a off hoff := by
  unfold fillSlots
  by_cases hk' : k = nSlots
  · simp only [hk', ↓reduceDIte]
  · simp only [hk', ↓reduceDIte]
    let step : IndexStep nSlots k (rowMul8_le hFit) hk hk' := {}
    let dstOff := dst + k * slotBytes
    have hDstNat : dstOff.toNat = dst.toNat + k.toNat * 8 :=
      slotAddr_toNat dst k step.hMul (slotOff_lt step.hlt hFit)
    have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le step.hlt hDst
    have hpair := suffixStepDisj off.toNat dst.toNat nSlots.toNat k.toNat hdisj step.hlt
    have hWriteDisj : off.toNat + 8 ≤ dstOff.toNat ∨ dstOff.toNat + 8 ≤ off.toNat := by
      rw [hDstNat]
      exact hpair.1
    have hdisj' : off.toNat + 8 ≤ dst.toNat + (k + 1).toNat * 8 ∨
        dst.toNat + nSlots.toNat * 8 ≤ off.toNat := by
      rw [step.hNext]
      exact hpair.2
    have hRec := fillSlots_outside dst nSlots v hFit (k + 1) step.hkNext
      (uset a dstOff v hWrite) (by rw [uset_size]; exact hDst) off
      (by rw [uset_size]; exact hoff) hdisj'
    have hKeep := uget_uset_disjoint a dstOff off v hWrite hoff hWriteDisj
    exact (uget_irrel _ _ _ _).trans (hRec.trans hKeep)
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact ({} : IndexStep nSlots k (rowMul8_le hFit) hk hk').hMeasure

/-- Slot `j` of the suffix that `fillSlots` still has to fill reads back as `v`. -/
private theorem fillSlots_uget (dst nSlots : USize) (v : UInt64)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (k : USize) (hk : k.toNat ≤ nSlots.toNat) (a : ByteArray)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (j : Nat) (hj : j < nSlots.toNat) (hkj : k.toNat ≤ j) :
    uget (fillSlots dst nSlots v hFit k hk a hDst) ((dst.toNat + j * 8).toUSize)
      (by
        rw [fillSlots_size dst nSlots v hFit k hk a hDst]
        rw [toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hFit)]
        exact slotOff_le hj hDst) = v := by
  unfold fillSlots
  by_cases hk' : k = nSlots
  · have hkNat : k.toNat = nSlots.toNat := by rw [hk']
    omega
  · simp only [hk', ↓reduceDIte]
    let step : IndexStep nSlots k (rowMul8_le hFit) hk hk' := {}
    let dstOff := dst + k * slotBytes
    have hDstNat : dstOff.toNat = dst.toNat + k.toNat * 8 :=
      slotAddr_toNat dst k step.hMul (slotOff_lt step.hlt hFit)
    have hWrite : dstOff.toNat + 8 ≤ a.size := by rw [hDstNat]; exact slotOff_le step.hlt hDst
    let a' := uset a dstOff v hWrite
    have hDst' : dst.toNat + nSlots.toNat * 8 ≤ a'.size := by rw [uset_size]; exact hDst
    by_cases hjk : j = k.toNat
    · have hTail : dstOff.toNat + 8 ≤ dst.toNat + (k + 1).toNat * 8 := by
        rw [hDstNat, step.hNext]
        omega
      have hOut := fillSlots_outside dst nSlots v hFit (k + 1) step.hkNext a' hDst'
        dstOff (by rw [uset_size]; exact hWrite) (Or.inl hTail)
      have hDstOff : dstOff = (dst.toNat + j * 8).toUSize := by
        apply USize.toNat_inj.mp
        rw [hDstNat, toNat_toUSize_of_lt_2_pow_32 (slotOff_lt hj hFit), hjk]
      have hStep := hOut.trans (uget_uset a dstOff v hWrite)
      exact (uget_congr (fillSlots dst nSlots v hFit (k + 1) step.hkNext a' hDst')
        dstOff ((dst.toNat + j * 8).toUSize) hDstOff _ _).symm.trans hStep
    · have hRec := fillSlots_uget dst nSlots v hFit (k + 1) step.hkNext a' hDst' j hj
        (by rw [step.hNext]; omega)
      exact (uget_irrel _ _ _ _).trans hRec
termination_by nSlots.toNat - k.toNat
decreasing_by
  exact ({} : IndexStep nSlots k (rowMul8_le hFit) hk hk').hMeasure

/-- Every slot of a filled row reads back as `v`. -/
theorem fillRow_uget (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    uget (fillRow a dst nSlots v hDst hFit) ((dst.toNat + j * 8).toUSize) hSlot = v := by
  unfold fillRow
  exact (uget_irrel _ _ _ _).trans
    (fillSlots_uget dst nSlots v hFit 0 (zero_le_toNat _) a hDst j hj (zero_le_toNat _))

/-- A slot that does not meet the filled row is unchanged. -/
theorem fillRow_uget_disjoint (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    uget (fillRow a dst nSlots v hDst hFit) off hSlot = uget a off hoff := by
  unfold fillRow
  exact (uget_irrel _ _ _ _).trans
    (fillSlots_outside dst nSlots v hFit 0 (zero_le_toNat _) a hDst off hoff
      (by simpa [USize.toNat_zero] using hdisj))

theorem SlotWord.sentinel {s : String} (h : s.utf8ByteSize + 1 < 2 ^ 64) :
    SlotWord s (sentinelWord s) := by
  refine Or.inl ?_
  unfold sentinelWord
  rw [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa using h)

theorem SlotWord.encode {s : String} (p : Pos s) (h : p.offset.byteIdx < 2 ^ 64) :
    SlotWord s (encodePos p) := by
  refine Or.inr ⟨p, ?_⟩
  unfold encodePos
  rw [Nat.toUInt64, UInt64.toNat_ofNat']
  exact Nat.mod_eq_of_lt (by simpa using h)

/-- A zero word is the start position. -/
theorem SlotWord.zero {s : String} : SlotWord s 0 :=
  Or.inr ⟨s.startPos, by simp [String.offset_startPos]⟩

/-- Every position of a string that fits in `UInt64` encodes as a capture word. -/
theorem SlotWord.of_pos {s : String} (p : Pos s) (h : s.utf8ByteSize + 1 < 2 ^ 64) :
    SlotWord s (encodePos p) := by
  apply SlotWord.encode
  have hle : p.offset.byteIdx ≤ s.utf8ByteSize := by simp
  omega

theorem uset_slotWord {s : String} (a : ByteArray) (off : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (hv : SlotWord s v)
    (hSlot : off.toNat + 8 ≤ (uset a off v h).size) :
    SlotWord s (uget (uset a off v h) off hSlot) := by
  rw [uget_uset_self]
  exact hv

theorem uset_slotWord_disjoint {s : String} (a : ByteArray) (off off' : USize) (v : UInt64)
    (h : off.toNat + 8 ≤ a.size) (h' : off'.toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a off' h'))
    (hdisj : off'.toNat + 8 ≤ off.toNat ∨ off.toNat + 8 ≤ off'.toNat)
    (hSlot : off'.toNat + 8 ≤ (uset a off v h).size) :
    SlotWord s (uget (uset a off v h) off' hSlot) := by
  rw [uget_uset_ne a off off' v h h' hdisj hSlot]
  exact hw

theorem fillRow_slotWord {s : String} (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hv : SlotWord s v) (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    SlotWord s (uget (fillRow a dst nSlots v hDst hFit) ((dst.toNat + j * 8).toUSize) hSlot) := by
  rw [fillRow_uget a dst nSlots v hDst hFit j hj hSlot]
  exact hv

theorem fillRow_slotWord_disjoint {s : String} (a : ByteArray) (dst nSlots : USize) (v : UInt64)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a off hoff))
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (fillRow a dst nSlots v hDst hFit).size) :
    SlotWord s (uget (fillRow a dst nSlots v hDst hFit) off hSlot) := by
  rw [fillRow_uget_disjoint a dst nSlots v hDst hFit off hoff hdisj hSlot]
  exact hw

theorem copyRow_slotWord {s : String} (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hsep : dst.toNat = src.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ src.toNat ∨
      src.toNat + nSlots.toNat * 8 ≤ dst.toNat)
    (j : Nat) (hj : j < nSlots.toNat)
    (hSlot : ((dst.toNat + j * 8).toUSize).toNat + 8 ≤
      (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size)
    (hSrcSlot : ((src.toNat + j * 8).toUSize).toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a ((src.toNat + j * 8).toUSize) hSrcSlot)) :
    SlotWord s (uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit)
      ((dst.toNat + j * 8).toUSize) hSlot) := by
  rw [copyRow_uget a dst src nSlots hDst hSrc hDstFit hSrcFit hsep j hj hSlot hSrcSlot]
  exact hw

theorem copyRow_slotWord_disjoint {s : String} (a : ByteArray) (dst src nSlots : USize)
    (hDst : dst.toNat + nSlots.toNat * 8 ≤ a.size)
    (hSrc : src.toNat + nSlots.toNat * 8 ≤ a.size)
    (hDstFit : dst.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (hSrcFit : src.toNat + nSlots.toNat * 8 ≤ 2 ^ 32)
    (off : USize) (hoff : off.toNat + 8 ≤ a.size)
    (hw : SlotWord s (uget a off hoff))
    (hdisj : off.toNat + 8 ≤ dst.toNat ∨ dst.toNat + nSlots.toNat * 8 ≤ off.toNat)
    (hSlot : off.toNat + 8 ≤ (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit).size) :
    SlotWord s (uget (copyRow a dst src nSlots hDst hSrc hDstFit hSrcFit) off hSlot) := by
  rw [copyRow_uget_disjoint a dst src nSlots hDst hSrc hDstFit hSrcFit off hoff hdisj hSlot]
  exact hw


end Regex.VM.FlatBuffer

end
