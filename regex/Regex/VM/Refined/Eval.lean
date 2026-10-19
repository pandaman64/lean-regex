module

public import Regex.VM.Refined.Basic

/-!
The tail-recursive PikeVM and the search built on it.
-/

public section

open Regex.Data (Anchor)
open Regex.VM.ClassTable (ClassTable)
open Regex.VM.FlatBuffer
open Regex.VM.Wide (WordArray toNat_u32_add_one toNat_add_of_lt_2_pow_32 toNat_mul_of_lt_2_pow_32
  toNat_u32_mul_ofNat)
open String (Pos PosPlusOne Slice)

namespace Regex.VM.Refined

/-- `1` while the closure is still the one started at the current position. -/
private def phaseRank (phase : UInt32) : Nat :=
  if phase = phaseClosure then 1 else 0

/--
Fuel for the ε-stack. A stepping phase sits strictly above every closure, so
entering a step-closure decreases the measure without moving `p`.
-/
private def closureFuel (phase : UInt32) (sp nCount n : Nat) : Nat :=
  if phase = phaseStep then
    3 * n + 2
  else
    sp + 2 * (n - nCount)

private def evalMeasure {s : String} (p : Pos s) (phase : UInt32) (cCount i : UInt32)
    (sp nCount n : Nat) : Nat × Nat × Nat × Nat :=
  (p.remainingBytes, phaseRank phase, cCount.toNat - i.toNat, closureFuel phase sp nCount n)

private theorem rem_next {s : String} {p : Pos s} (h : p ≠ s.endPos) :
    (p.next h).remainingBytes < p.remainingBytes :=
  (Pos.lt_iff_remainingBytes_lt p (p.next h)).mp p.lt_next

private abbrev EvalRel :=
  Prod.Lex (fun a b : Nat => a < b)
    (Prod.Lex (fun a b : Nat => a < b)
      (Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b)))

private theorem lex4_1 {a a' : Nat} {b b' c c' d d' : Nat} (h : a' < a) :
    EvalRel (a', b', c', d') (a, b, c, d) :=
  Prod.Lex.left (b', c', d') (b, c, d) h

private theorem lex4_2 {a b b' : Nat} {c c' d d' : Nat} (h : b' < b) :
    EvalRel (a, b', c', d') (a, b, c, d) :=
  Prod.Lex.right a (Prod.Lex.left (c', d') (c, d) h)

private theorem lex4_3 {a b c c' d d' : Nat} (h : c' < c) :
    EvalRel (a, b, c', d') (a, b, c, d) :=
  Prod.Lex.right a (Prod.Lex.right b (Prod.Lex.left d' d h))

private theorem lex4_4 {a b c d d' : Nat} (h : d' < d) :
    EvalRel (a, b, c, d') (a, b, c, d) :=
  Prod.Lex.right a (Prod.Lex.right b (Prod.Lex.right c h))

private theorem phase_beq_step (phase : UInt32) :
    (phase == phaseStep) = true ↔ phase = phaseStep := by
  simp [beq_iff_eq]

private theorem closureFuel_notStep {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) :
    closureFuel phase sp nCount n = sp + 2 * (n - nCount) := by
  simp [closureFuel, h]

private theorem closureFuel_lt {phase : UInt32} {sp sp' nCount nCount' n : Nat}
    (h : ¬ phase = phaseStep)
    (hlt : sp' + 2 * (n - nCount') < sp + 2 * (n - nCount)) :
    closureFuel phase sp' nCount' n < closureFuel phase sp nCount n := by
  rw [closureFuel_notStep h, closureFuel_notStep h]
  exact hlt

private theorem fuel_pop {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hsp : 0 < sp) :
    closureFuel phase (sp - 1) nCount n < closureFuel phase sp nCount n :=
  closureFuel_lt h (by omega)

private theorem fuel_keep {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hc : nCount < n) :
    closureFuel phase sp (nCount + 1) n < closureFuel phase sp nCount n :=
  closureFuel_lt h (by omega)

private theorem fuel_split {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hc : nCount < n) :
    closureFuel phase (sp + 1) (nCount + 1) n < closureFuel phase sp nCount n :=
  closureFuel_lt h (by omega)

/-- A popped state that is not pushed back, after it has been inserted. -/
private theorem fuel_discard {phase : UInt32} {sp nCount n : Nat}
    (h : ¬ phase = phaseStep) (hsp : 0 < sp) (hc : nCount < n) :
    closureFuel phase (sp - 1) (nCount + 1) n < closureFuel phase sp nCount n :=
  closureFuel_lt h (by omega)

private theorem fuel_enter (nCount n : Nat) (hc : nCount ≤ n) :
    closureFuel phaseStepClosure 1 nCount n < closureFuel phaseStep 0 nCount n := by
  have hne : phaseStepClosure ≠ phaseStep := by decide
  have hlt : 1 + 2 * (n - nCount) < 3 * n + 2 := by omega
  calc
    closureFuel phaseStepClosure 1 nCount n = 1 + 2 * (n - nCount) := by
      simp [closureFuel, hne]
    _ < 3 * n + 2 := hlt
    _ = closureFuel phaseStep 0 nCount n := by
      simp [closureFuel]

private theorem step_sub_succ {c i : UInt32} (h : i.toNat < c.toNat) :
    c.toNat - (i + 1).toNat < c.toNat - i.toNat := by
  have hsucc : (i + 1).toNat = i.toNat + 1 :=
    toNat_u32_add_one (by
      have := UInt32.toNat_lt c
      omega)
  rw [hsucc]
  exact Nat.sub_succ_lt_self _ _ h

private theorem rank_closure : phaseRank phaseClosure = 1 := by
  unfold phaseRank
  decide

private theorem rank_step : phaseRank phaseStep = 0 := by
  unfold phaseRank
  decide

private theorem rank_stepClosure : phaseRank phaseStepClosure = 0 := by
  unfold phaseRank
  decide

private theorem dec_rem {s : String} {p p' : Pos s} {phase phase' : UInt32}
    {cCount cCount' i i' : UInt32} {sp sp' nCount nCount' n : Nat}
    (h : p'.remainingBytes < p.remainingBytes) :
    EvalRel (evalMeasure p' phase' cCount' i' sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  unfold evalMeasure
  exact lex4_1 h

private theorem dec_rank {s : String} {p q : Pos s} {phase phase' : UInt32}
    {cCount cCount' i i' : UInt32} {sp sp' nCount nCount' n : Nat}
    (hq : q = p) (h : phaseRank phase' < phaseRank phase) :
    EvalRel (evalMeasure q phase' cCount' i' sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  subst hq
  unfold evalMeasure
  exact lex4_2 h

private theorem dec_step {s : String} {p : Pos s} {phase : UInt32}
    {cCount i i' : UInt32} {sp sp' nCount nCount' n : Nat}
    (h : cCount.toNat - i'.toNat < cCount.toNat - i.toNat) :
    EvalRel (evalMeasure p phase cCount i' sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  unfold evalMeasure
  exact lex4_3 h

/-- Step-closure gave up: `i` advances and the phase returns to stepping. Both ranks are `0`. -/
private theorem dec_resume {s : String} {p : Pos s} {cCount i : UInt32}
    {sp sp' nCount nCount' n : Nat}
    (h : cCount.toNat - (i + 1).toNat < cCount.toNat - i.toNat) :
    EvalRel (evalMeasure p phaseStep cCount (i + 1) sp' nCount' n)
      (evalMeasure p phaseStepClosure cCount i sp nCount n) := by
  unfold evalMeasure phaseRank
  exact lex4_3 h

private theorem dec_fuel {s : String} {p : Pos s} {phase : UInt32} {cCount i : UInt32}
    {sp sp' nCount nCount' n : Nat}
    (h : closureFuel phase sp' nCount' n < closureFuel phase sp nCount n) :
    EvalRel (evalMeasure p phase cCount i sp' nCount' n)
      (evalMeasure p phase cCount i sp nCount n) := by
  unfold evalMeasure
  exact lex4_4 h

private theorem fuel_enter_at (sp nCount n : Nat) (hc : nCount ≤ n) :
    closureFuel phaseStepClosure 1 nCount n < closureFuel phaseStep sp nCount n := by
  have hne : ¬ phaseStepClosure = phaseStep := by decide
  have hlt := fuel_enter nCount n hc
  rw [closureFuel_notStep hne] at hlt
  rw [closureFuel_notStep hne]
  simpa [closureFuel] using hlt

private theorem u32_toNat_ne {a b : UInt32} (h : ¬ a = b) : a.toNat ≠ b.toNat := by
  intro heq
  exact h (UInt32.toNat_inj.mp heq)

private theorem phase_stepClosure_of (phase : UInt32)
    (h : phase = phaseClosure ∨ phase = phaseStepClosure ∨ phase = phaseStep)
    (hnot : ¬ phase = phaseStep) (hnotC : ¬ phase = phaseClosure) :
    phase = phaseStepClosure := by
  rcases h with h | h | h
  · exact absurd h hnotC
  · exact h
  · exact absurd h hnot

private theorem CpRel.closure {s : String} (p : Pos s) : CpRel phaseClosure p p :=
  ⟨fun _ => rfl, fun h => absurd h (by decide : phaseClosure ≠ phaseStepClosure)⟩

private theorem CpRel.step {s : String} (p cp : Pos s) : CpRel phaseStep p cp :=
  ⟨fun h => absurd h (by decide : phaseStep ≠ phaseClosure),
    fun h => absurd h (by decide : phaseStep ≠ phaseStepClosure)⟩

private theorem CpRel.stepHit {s : String} {p : Pos s} (hp : p ≠ s.endPos) :
    CpRel phaseStepClosure p (p.next hp) :=
  ⟨fun h => absurd h (by decide : phaseStepClosure ≠ phaseClosure), fun _ => rem_next hp⟩

private theorem SetInv.not_mem_of_miss {den spa : WordArray} {count state si : Nat}
    (hsi : wordAt spa (4 * state) = si.toUInt32) (hsiLt : si < UInt32.size)
    (hmiss : ¬ (si < count ∧ (wordAt den (4 * si)).toNat = state)) :
    ¬ SetMem den spa count state := by
  intro hmem
  have hto : (wordAt spa (4 * state)).toNat = si := by
    rw [hsi, toNat_toUInt32_of_lt hsiLt]
  unfold SetMem at hmem
  rw [hto] at hmem
  exact hmiss hmem

/-- Return to the stepping phase at `p`, with the step cursor set to `i'`. -/
private theorem RunInv.toStep {s : String}
    {words : WordArray} {classes : Array ClassTable} {start : UInt32}
    {nSlots : Nat} {nStates : UInt32} {slots cRow0 nRow0 stackRow0 : USize}
    {p cp : Pos s} {cCount : UInt32} {cDen cSpa : WordArray}
    {nCount : UInt32} {nDen nSpa stkS : WordArray} {caps : ByteArray}
    {sp : Nat} {phase i : UInt32} {sent : UInt64}
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i sent)
    (i' : UInt32) (hi : i'.toNat ≤ cCount.toNat) :
    RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p p cCount cDen cSpa nCount nDen nSpa stkS caps sp phaseStep i' sent where
  words := h.words
  start_lt := h.start_lt
  curr := h.curr
  next := h.next
  stack := h.stack
  buf := h.buf
  i_le := hi
  sp_le := h.sp_le
  phase_ok := Or.inr (Or.inr rfl)
  cp_rel := CpRel.step p p
  step_i := fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure)
  hlen := h.hlen
  sentOk := h.sentOk
  capsOk := h.capsOk

private theorem RunInv.advance {s : String}
    {words : WordArray} {classes : Array ClassTable} {start : UInt32}
    {nSlots : Nat} {nStates : UInt32} {slots cRow0 nRow0 stackRow0 : USize}
    {p cp : Pos s} {cCount : UInt32} {cDen cSpa : WordArray}
    {nCount : UInt32} {nDen nSpa stkS : WordArray} {caps : ByteArray}
    {sp : Nat} {phase i : UInt32} {sent : UInt64}
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i sent)
    (hi : (i + 1).toNat ≤ cCount.toNat) :
    RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p p cCount cDen cSpa nCount nDen nSpa stkS caps sp phaseStep (i + 1) sent :=
  toStep h (i + 1) hi

private theorem RunInv.giveUp {s : String}
    {words : WordArray} {classes : Array ClassTable} {start : UInt32}
    {nSlots : Nat} {nStates : UInt32} {slots cRow0 nRow0 stackRow0 : USize}
    {p cp : Pos s} {cCount : UInt32} {cDen cSpa : WordArray}
    {nCount : UInt32} {nDen nSpa stkS : WordArray} {caps : ByteArray}
    {sp : Nat} {phase i : UInt32} {sent : UInt64}
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i sent) :
    RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p p cCount cDen cSpa nCount nDen nSpa stkS caps sp phaseStep cCount sent :=
  toStep h cCount (Nat.le_refl _)

/--
Tail-recursive PikeVM. Every recursive call is in tail position so the buffers stay unique.
`c*` is the set being read, `n*` the set being written. Capture slots live in `caps`; `cRow0`
and `nRow0` are the first rows of those two sets and are swapped, not copied, when a closure
finishes. `clos` means row 1 holds the match found by the closure in progress; `matched` means
row 0 holds the match already accepted.

`p` is the position of the active `eachStepChar` loop. `cp` is the position of the closure
(where saves and anchors run). They differ only while a character transition's closure is in
progress: the remaining states of this character must still be tested at `p` if that closure
does not reach `.done`.
-/
def eval {s : String}
    (words : WordArray) (classes : Array ClassTable) (start : UInt32)
    (nSlots : Nat) (nStates : UInt32) (slots : USize) (sent : UInt64)
    (cRow0 nRow0 stackRow0 : USize)
    (p cp : Pos s) (matched clos : Bool)
    (cCount : UInt32) (cDen cSpa : WordArray)
    (nCount : UInt32) (nDen nSpa : WordArray)
    (stkS : WordArray) (caps : ByteArray) (sp : Nat)
    (phase i : UInt32)
    (h : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
      p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp phase i sent) :
    SearchRun (s := s) nSlots nStates :=
  if hstep : phase == phaseStep then
    have hphase : phase = phaseStep := (beq_iff_eq).mp hstep
    if hp : p = s.endPos then
      SearchRun.pack matched nSlots nStates cDen cSpa nDen nSpa stkS caps
        ⟨h.capsOk, h.curr.clear, h.next.clear, h.stack.clear, h.buf.stk_ge,
          h.buf.rows_size, h.buf.rows_fit⟩
    else if i == 0 && cCount == 0 && matched then
      SearchRun.pack matched nSlots nStates cDen cSpa nDen nSpa stkS caps
        ⟨h.capsOk, h.curr.clear, h.next.clear, h.stack.clear, h.buf.stk_ge,
          h.buf.rows_size, h.buf.rows_fit⟩
    else if hic : i == cCount then
      if !matched then
        have hroom : 0 < stkS.size := by
          have := h.buf.stk_ge
          omega
        have hrowLt : 2 + 2 * nStates.toNat < 2 + 2 * nStates.toNat + stkS.size := by
          have := h.buf.stk_ge
          omega
        have hw := h.buf.window stackRow0 (2 + 2 * nStates.toNat) (Or.inr h.buf.stack_row) hrowLt
        let caps := fillRow caps (rowOff stackRow0 slots) slots sent hw.1 hw.2
        let stkS := stkS.usetWord 0 start (h.stack.wordBound 0 hroom (by decide))
        have hstack : StackInv stkS 1 nStates.toNat := by
          simp only [stkS]
          exact h.stack.reset hroom start h.start_lt
        have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
          simp only [caps, stkS]
          exact (h.buf.of_size (fillRow_size _ _ _ _ hw.1 hw.2) rfl).of_size rfl (by
            rw [WordArray.usetWord_eq]
            exact (WordArray.size_uset _ _ _ _).2)
        have hcaps : CapsWf (s := s) caps nSlots (2 + 2 * nStates.toNat + stkS.size) := by
          simp only [caps, stkS]
          rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
          exact CapsWf.fillAt h.capsOk h.buf rfl stackRow0 (2 + 2 * nStates.toNat)
            (Or.inr h.buf.stack_row) hrowLt sent h.sentOk hw.1 hw.2
        have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
            (p.next hp) (p.next hp) cCount cDen cSpa nCount nDen nSpa stkS caps 1
            phaseClosure 0 sent :=
          ⟨h.words, h.start_lt, h.curr, h.next, hstack, hbuf,
            by
              rw [UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)]
              exact Nat.zero_le _,
            Nat.le_add_left 1 _, Or.inl rfl, CpRel.closure (p.next hp),
            fun hc => absurd hc (by decide : phaseClosure ≠ phaseStepClosure),
            h.hlen, h.sentOk, hcaps⟩
        have hlt : EvalRel
            (evalMeasure (p.next hp) phaseClosure cCount 0 1 nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
          dec_rem (rem_next hp)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          (p.next hp) (p.next hp) false false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps 1
          phaseClosure 0 h'
      else
        have hz : (0 : UInt32).toNat = 0 :=
          UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)
        have h' : RunInv words classes start nSlots nStates slots nRow0 cRow0 stackRow0
            (p.next hp) (p.next hp) nCount nDen nSpa 0 cDen cSpa stkS caps 0
            phaseStep 0 sent :=
          ⟨h.words, h.start_lt, h.next,
            by rw [hz]; exact h.curr.clear,
            h.stack.clear,
            h.buf.swap,
            by rw [hz]; exact Nat.zero_le _,
            by rw [hz]; exact Nat.zero_le _,
            Or.inr (Or.inr rfl), CpRel.step (p.next hp) (p.next hp),
            fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure),
            h.hlen, h.sentOk, h.capsOk⟩
        have hlt : EvalRel
            (evalMeasure (p.next hp) phaseStep nCount 0 0 (0 : UInt32).toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
          dec_rem (rem_next hp)
        eval words classes start nSlots nStates slots sent nRow0 cRow0 stackRow0
          (p.next hp) (p.next hp) matched false
          nCount nDen nSpa
          (0 : UInt32) cDen cSpa
          stkS caps 0
          phaseStep 0 h'
    else
      have hne : ¬ i = cCount := fun heq => hic ((beq_iff_eq).mpr heq)
      have hltI : i.toNat < cCount.toNat := Nat.lt_of_le_of_ne h.i_le (u32_toNat_ne hne)
      have hi1 : (i + 1).toNat ≤ cCount.toNat := by
        rw [toNat_u32_add_one (by
          have := hltI
          have := h.curr.count_le
          have := h.words.le_30
          omega)]
        exact Nat.succ_le_of_lt hltI
      have hlt : EvalRel
          (evalMeasure p phaseStep cCount (i + 1) sp nCount.toNat nStates.toNat)
          (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
        rw [hphase]
        exact dec_step (step_sub_succ hltI)
      have hstateB : (i.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ cDen.data.size := by
        rw [u32_usize i]
        exact h.curr.denBound i.toNat (Nat.lt_of_lt_of_le hltI h.curr.count_le)
      let state := cDen.ugetWord i.toUSize hstateB
      have hs : state.toNat < nStates.toNat := by
        simp only [state]
        rw [ugetWord_wordAt cDen i hstateB
          (Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hltI h.curr.count_le) h.curr.n_fit)]
        exact h.curr.dense_lt i.toNat hltI
      have htagB := h.words.tagBound state hs
      have h4n : ((4 : USize)).toNat = 4 :=
        Regex.VM.Wide.toNat_uSize_ofNat_of_lt 4 (by decide)
      have h8n : ((8 : USize)).toNat = 8 :=
        Regex.VM.Wide.toNat_uSize_ofNat_of_lt 8 (by decide)
      have hoff4 := h.words.offBound state hs 4 (by rw [h4n]; decide)
      have hoff8 := h.words.offBound state hs 8 (by rw [h8n]; decide)
      have hroom : 0 < stkS.size := by
        have := h.buf.stk_ge
        omega
      have hrowLt : 2 + 2 * nStates.toNat < 2 + 2 * nStates.toNat + stkS.size := by
        have := h.buf.stk_ge
        omega
      have hdstW := h.buf.window stackRow0 (2 + 2 * nStates.toNat) (Or.inr h.buf.stack_row) hrowLt
      have haddC := h.buf.addU32 cRow0 h.buf.c_row state hs
      have hsrcW := h.buf.window (cRow0 + state.toUSize) (cRow0.toNat + state.toNat) haddC.1 haddC.2
      let base := state.toUSize * strideBytes
      let tag := words.uget base htagB
      if tag == tagDone then
        have hlt : EvalRel
            (evalMeasure p phaseStep cCount cCount sp nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
          rw [hphase]
          exact dec_step (by rw [Nat.sub_self]; exact Nat.sub_pos_of_lt hltI)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep cCount h.giveUp
      else if tag == tagChar then
        let extra := words.uget (base + 8) hoff8.1
        if (p.get hp).val == extra then
          let nextW := words.uget (base + 4) hoff4.1
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots hdstW.1 hsrcW.1 hdstW.2 hsrcW.2
          have hnextLt : nextW.toNat < nStates.toNat := by
            simp only [nextW]
            rw [h.words.word_eq state hs 4 (Or.inl h4n) hoff4.1, h4n]
            exact h.words.next_lt state.toNat hs
          let stkS := stkS.usetWord 0 nextW (h.stack.wordBound 0 hroom (by decide))
          have hstack : StackInv stkS 1 nStates.toNat := by
            simp only [stkS]
            exact h.stack.reset hroom nextW hnextLt
          have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
            simp only [caps, stkS]
            exact (h.buf.of_size (copyRow_size _ _ _ _ hdstW.1 hsrcW.1 hdstW.2 hsrcW.2) rfl).of_size
              rfl (by
                rw [WordArray.usetWord_eq]
                exact (WordArray.size_uset _ _ _ _).2)
          have hcaps : CapsWf (s := s) caps nSlots (2 + 2 * nStates.toNat + stkS.size) := by
            simp only [caps, stkS]
            rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
            exact CapsWf.copyAt h.capsOk h.buf rfl stackRow0 (cRow0 + state.toUSize)
              (2 + 2 * nStates.toNat) (cRow0.toNat + state.toNat)
              (Or.inr h.buf.stack_row) haddC.1 hrowLt haddC.2
              hdstW.1 hsrcW.1 hdstW.2 hsrcW.2
          have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
              p (p.next hp) cCount cDen cSpa nCount nDen nSpa stkS caps 1
              phaseStepClosure i sent :=
            ⟨h.words, h.start_lt, h.curr, h.next, hstack, hbuf, h.i_le,
              Nat.le_add_left 1 _, Or.inr (Or.inl rfl), CpRel.stepHit hp, fun _ => hltI,
              h.hlen, h.sentOk, hcaps⟩
          have hlt : EvalRel
              (evalMeasure p phaseStepClosure cCount i 1 nCount.toNat nStates.toNat)
              (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
            unfold evalMeasure
            rw [hphase]
            unfold phaseRank
            exact lex4_4 (fuel_enter_at sp nCount.toNat nStates.toNat h.next.count_le)
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p (p.next hp) matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps 1
            phaseStepClosure i h'
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p p matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp
            phaseStep (i + 1) (h.advance hi1)
      else if hsparse : tag == tagSparse then
        let extra := words.uget (base + 8) hoff8.1
        have hcls : extra.toNat < classes.size := by
          simp only [extra]
          rw [h.words.word_eq state hs 8 (Or.inr h8n) hoff8.1, h8n]
          exact h.words.sparse_lt state.toNat hs (by
            have htag : tag = wordAt words (12 * state.toNat) := by
              simp only [tag, base]
              exact h.words.tag_eq state hs htagB
            rw [← htag]
            exact (beq_iff_eq).mp hsparse)
        let cs := classes.uget extra.toUSize (by rw [UInt32.toNat_toUSize]; exact hcls)
        if cs.contains (p.get hp) then
          let nextW := words.uget (base + 4) hoff4.1
          let caps := copyRow caps (rowOff stackRow0 slots)
            (rowOff (cRow0 + state.toUSize) slots) slots hdstW.1 hsrcW.1 hdstW.2 hsrcW.2
          have hnextLt : nextW.toNat < nStates.toNat := by
            simp only [nextW]
            rw [h.words.word_eq state hs 4 (Or.inl h4n) hoff4.1, h4n]
            exact h.words.next_lt state.toNat hs
          let stkS := stkS.usetWord 0 nextW (h.stack.wordBound 0 hroom (by decide))
          have hstack : StackInv stkS 1 nStates.toNat := by
            simp only [stkS]
            exact h.stack.reset hroom nextW hnextLt
          have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
            simp only [caps, stkS]
            exact (h.buf.of_size (copyRow_size _ _ _ _ hdstW.1 hsrcW.1 hdstW.2 hsrcW.2) rfl).of_size
              rfl (by
                rw [WordArray.usetWord_eq]
                exact (WordArray.size_uset _ _ _ _).2)
          have hcaps : CapsWf (s := s) caps nSlots (2 + 2 * nStates.toNat + stkS.size) := by
            simp only [caps, stkS]
            rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
            exact CapsWf.copyAt h.capsOk h.buf rfl stackRow0 (cRow0 + state.toUSize)
              (2 + 2 * nStates.toNat) (cRow0.toNat + state.toNat)
              (Or.inr h.buf.stack_row) haddC.1 hrowLt haddC.2
              hdstW.1 hsrcW.1 hdstW.2 hsrcW.2
          have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
              p (p.next hp) cCount cDen cSpa nCount nDen nSpa stkS caps 1
              phaseStepClosure i sent :=
            ⟨h.words, h.start_lt, h.curr, h.next, hstack, hbuf, h.i_le,
              Nat.le_add_left 1 _, Or.inr (Or.inl rfl), CpRel.stepHit hp, fun _ => hltI,
              h.hlen, h.sentOk, hcaps⟩
          have hlt : EvalRel
              (evalMeasure p phaseStepClosure cCount i 1 nCount.toNat nStates.toNat)
              (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
            unfold evalMeasure
            rw [hphase]
            unfold phaseRank
            exact lex4_4 (fuel_enter_at sp nCount.toNat nStates.toNat h.next.count_le)
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p (p.next hp) matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps 1
            phaseStepClosure i h'
        else
          eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
            p p matched false
            cCount cDen cSpa
            nCount nDen nSpa
            stkS caps sp
            phaseStep (i + 1) (h.advance hi1)
      else
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp
          phaseStep (i + 1) (h.advance hi1)
  else
    have hnotStep : ¬ phase = phaseStep := fun heq => hstep ((beq_iff_eq).mpr heq)
    if hsp0 : sp == 0 then
      have hspZ : sp = 0 := (beq_iff_eq).mp hsp0
      if hfin : phase == phaseClosure || clos then
        have h0n : ((0 : USize)).toNat = 0 := USize.toNat_zero
        have h1n : ((1 : USize)).toNat = 1 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 1 (by decide)
        have hlt0 : 0 < 2 + 2 * nStates.toNat + stkS.size := by omega
        have hlt1 : 1 < 2 + 2 * nStates.toNat + stkS.size := by omega
        have hw0 := h.buf.window 0 0 (Or.inr h0n) hlt0
        have hw1 := h.buf.window 1 1 (Or.inr h1n) hlt1
        let caps :=
          if clos then
            copyRow caps (rowOff 0 slots) (rowOff 1 slots) slots hw0.1 hw1.1 hw0.2 hw1.2
          else
            caps
        have hz : (0 : UInt32).toNat = 0 :=
          UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)
        have hbuf : EvalBuf caps stkS slots nRow0 cRow0 stackRow0 nSlots nStates.toNat := by
          simp only [caps]
          split
          · exact (h.buf.swap).of_size (copyRow_size _ _ _ _ hw0.1 hw1.1 hw0.2 hw1.2) rfl
          · exact h.buf.swap
        have hcaps : CapsWf (s := s) caps nSlots (2 + 2 * nStates.toNat + stkS.size) := by
          simp only [caps]
          split
          · exact CapsWf.copyAt h.capsOk h.buf rfl 0 1 0 1 (Or.inr h0n) (Or.inr h1n)
              hlt0 hlt1 hw0.1 hw1.1 hw0.2 hw1.2
          · exact h.capsOk
        have h' : RunInv words classes start nSlots nStates slots nRow0 cRow0 stackRow0
            cp cp nCount nDen nSpa 0 cDen cSpa stkS caps 0 phaseStep 0 sent :=
          ⟨h.words, h.start_lt, h.next,
            by rw [hz]; exact h.curr.clear,
            hspZ ▸ h.stack,
            hbuf,
            by rw [hz]; exact Nat.zero_le _,
            by rw [hz]; exact Nat.zero_le _,
            Or.inr (Or.inr rfl), CpRel.step cp cp,
            fun hc => absurd hc (by decide : phaseStep ≠ phaseStepClosure),
            h.hlen, h.sentOk, hcaps⟩
        have hlt : EvalRel
            (evalMeasure cp phaseStep nCount 0 0 (0 : UInt32).toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
          by_cases hph : phase = phaseClosure
          · exact dec_rank (h.cp_rel.1 hph) (by rw [hph, rank_step, rank_closure]; decide)
          · exact dec_rem (h.cp_rel.2 (phase_stepClosure_of phase h.phase_ok hnotStep hph))
        eval words classes start nSlots nStates slots sent nRow0 cRow0 stackRow0
          cp cp clos false
          nCount nDen nSpa
          (0 : UInt32) cDen cSpa
          stkS caps 0
          phaseStep 0 h'
      else
        have hnotC : ¬ phase = phaseClosure := by
          intro hph
          apply hfin
          rw [hph]
          simp [Bool.true_or]
        have hsc := phase_stepClosure_of phase h.phase_ok hnotStep hnotC
        have hltI := h.step_i hsc
        have hi1 : (i + 1).toNat ≤ cCount.toNat := by
          rw [toNat_u32_add_one (by
            have := hltI
            have := h.curr.count_le
            have := h.words.le_30
            omega)]
          exact Nat.succ_le_of_lt hltI
        have hlt : EvalRel
            (evalMeasure p phaseStep cCount (i + 1) 0 nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) := by
          rw [hsc]
          exact dec_resume (step_sub_succ hltI)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p p matched false
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps 0
          phaseStep (i + 1) (hspZ ▸ h.advance hi1)
    else
      have hspPos : 0 < sp := by
        have hnez : sp ≠ 0 := fun h0 => hsp0 ((beq_iff_eq).mpr h0)
        omega
      let sp' := sp - 1
      have hspLt : sp' < sp := Nat.sub_lt hspPos (by decide)
      have hsp30 : sp' < 2 ^ 30 := Nat.lt_of_lt_of_le hspLt h.stack.sp_fit
      have hstkB := h.stack.wordBound sp' (Nat.lt_of_lt_of_le hspLt h.stack.sp_le) hsp30
      let stkOff := rowOff (stackRow0 + sp'.toUSize) slots
      let state := stkS.ugetWord sp'.toUSize hstkB
      have hs : state.toNat < nStates.toNat := by
        simp only [state]
        rw [h.stack.readWord sp' hspLt]
        exact h.stack.id_lt sp' hspLt
      have hspaB : (state.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ nSpa.data.size := by
        rw [u32_usize state]
        exact h.next.spaBound state.toNat hs
      let si := nSpa.ugetWord state.toUSize hspaB
      let seen :=
        if hsi : si < nCount then
          nDen.ugetWord si.toUSize (by
            rw [u32_usize si]
            exact h.next.denBound si.toNat
              (Nat.lt_of_lt_of_le (UInt32.lt_iff_toNat_lt.mp hsi) h.next.count_le)) == state
        else
          false
      if hseenB : seen = true then
        have hstack : StackInv stkS sp' nStates.toNat := by
          simpa [sp'] using h.stack.pop hspPos
        have hspLe : sp' ≤ nCount.toNat + 1 := Nat.le_trans (Nat.le_of_lt hspLt) h.sp_le
        have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
            p cp cCount cDen cSpa nCount nDen nSpa stkS caps sp' phase i sent :=
          ⟨h.words, h.start_lt, h.curr, h.next, hstack, h.buf, h.i_le, hspLe,
            h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, h.capsOk⟩
        have hlt : EvalRel
            (evalMeasure p phase cCount i (sp - 1) nCount.toNat nStates.toNat)
            (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
          dec_fuel (fuel_pop hnotStep hspPos)
        eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
          p cp matched clos
          cCount cDen cSpa
          nCount nDen nSpa
          stkS caps sp'
          phase i h'
      else
        have hnot : ¬ SetMem nDen nSpa nCount.toNat state.toNat := by
          have hread : wordAt nSpa (4 * state.toNat) = si := by
            simp only [si]
            exact (ugetWord_wordAt nSpa state hspaB
              (Nat.lt_of_lt_of_le hs h.next.n_fit)).symm
          apply SetInv.not_mem_of_miss (si := si.toNat)
            (by rw [hread]; exact (UInt32.ofNat_toNat).symm)
            (UInt32.toNat_lt si)
          intro hbad
          have hltSi : si < nCount := (UInt32.lt_iff_toNat_lt).mpr hbad.1
          have hsiFit : si.toNat < 2 ^ 30 :=
            Nat.lt_of_lt_of_le (Nat.lt_of_lt_of_le hbad.1 h.next.count_le) h.next.n_fit
          have hdenB : (si.toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ nDen.data.size := by
            rw [u32_usize si]
            exact h.next.denBound si.toNat (Nat.lt_of_lt_of_le hbad.1 h.next.count_le)
          have hword : nDen.ugetWord si.toUSize hdenB = state := by
            rw [ugetWord_wordAt nDen si hdenB hsiFit]
            have hEq : wordAt nDen (4 * si.toNat) = state.toNat.toUInt32 :=
              UInt32.toNat_inj.mp (by
                rw [hbad.2, toNat_toUInt32_of_lt (UInt32.toNat_lt state)])
            rw [hEq]
            exact UInt32.ofNat_toNat
          have hseen : seen = true := by
            simp only [seen]
            rw [dite_eq_left hltSi, hword]
            simp
          exact absurd hseen hseenB
        have hcountLt : nCount.toNat < nStates.toNat :=
          SetInv.lt_of_not_mem h.next state.toNat hs hnot
        have hcnt : nCount.toNat + 1 < 2 ^ 32 := by
          have := hcountLt
          have := h.words.le_30
          omega
        have htagB := h.words.tagBound state hs
        have h4n : ((4 : USize)).toNat = 4 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 4 (by decide)
        have h8n : ((8 : USize)).toNat = 8 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 8 (by decide)
        have hoff4 := h.words.offBound state hs 4 (by rw [h4n]; decide)
        have hoff8 := h.words.offBound state hs 8 (by rw [h8n]; decide)
        let base := state.toUSize * strideBytes
        let tag := words.uget base htagB
        let nextW := words.uget (base + 4) hoff4.1
        let extra := words.uget (base + 8) hoff8.1
        have h1n : ((1 : USize)).toNat = 1 :=
          Regex.VM.Wide.toNat_uSize_ofNat_of_lt 1 (by decide)
        have hlt1 : 1 < 2 + 2 * nStates.toNat + stkS.size := by omega
        have hw1 := h.buf.window 1 1 (Or.inr h1n) hlt1
        have hslot := h.buf.stackSlot sp' (Nat.lt_of_lt_of_le hspLt h.stack.sp_le)
          (Nat.lt_trans hsp30 (by decide : 2 ^ 30 < 2 ^ 32))
        have hstkW := h.buf.window (stackRow0 + sp'.toUSize) (2 + 2 * nStates.toNat + sp')
          hslot.1 hslot.2
        have haddN := h.buf.addU32 nRow0 h.buf.n_row state hs
        have hnextW := h.buf.window (nRow0 + state.toUSize) (nRow0.toNat + state.toNat)
          haddN.1 haddN.2
        let caps1 :=
          if tag == tagDone && !clos then
            copyRow caps (rowOff 1 slots) stkOff slots hw1.1 hstkW.1 hw1.2 hstkW.2
          else
            caps
        have hsz1 : caps1.size = caps.size := by
          simp only [caps1]
          split
          · exact copyRow_size _ _ _ _ hw1.1 hstkW.1 hw1.2 hstkW.2
          · rfl
        let clos := tag == tagDone || clos
        have hnext1 :
            (rowOff (nRow0 + state.toUSize) slots).toNat + slots.toNat * 8 ≤ caps1.size := by
          rw [hsz1]
          exact hnextW.1
        have hstk1 : stkOff.toNat + slots.toNat * 8 ≤ caps1.size := by
          rw [hsz1]
          simp only [stkOff]
          exact hstkW.1
        let caps2 :=
          if writesUpdate tag then
            copyRow caps1 (rowOff (nRow0 + state.toUSize) slots) stkOff slots
              hnext1 hstk1 hnextW.2 hstkW.2
          else
            caps1
        have hsz2 : caps2.size = caps.size := by
          simp only [caps2]
          split
          · rw [copyRow_size _ _ _ _ hnext1 hstk1 hnextW.2 hstkW.2, hsz1]
          · exact hsz1
        have hcaps1 : CapsWf (s := s) caps1 nSlots (2 + 2 * nStates.toNat + stkS.size) := by
          simp only [caps1]
          split
          · exact CapsWf.copyAt h.capsOk h.buf rfl 1 (stackRow0 + sp'.toUSize) 1
              (2 + 2 * nStates.toNat + sp') (Or.inr h1n) hslot.1 hlt1 hslot.2
              hw1.1 hstkW.1 hw1.2 hstkW.2
          · exact h.capsOk
        have hsrcNat : stkOff.toNat = (2 + 2 * nStates.toNat + sp') * nSlots * 8 := by
          simp only [stkOff]
          exact h.buf.rowOff_eq (stackRow0 + sp'.toUSize) (2 + 2 * nStates.toNat + sp')
            hslot.1 hslot.2
        have hcaps2 : CapsWf (s := s) caps2 nSlots (2 + 2 * nStates.toNat + stkS.size) := by
          simp only [caps2]
          split
          · exact CapsWf.copyRow hcaps1 (rowOff (nRow0 + state.toUSize) slots) stkOff slots
              (nRow0.toNat + state.toNat) (2 + 2 * nStates.toNat + sp')
              (h.buf.rowOff_eq (nRow0 + state.toUSize) (nRow0.toNat + state.toNat) haddN.1 haddN.2)
              hsrcNat h.buf.slots_eq haddN.2 hslot.2 hnext1 hstk1 hnextW.2 hstkW.2
          · exact hcaps1
        let nDen := nDen.usetWord nCount.toUSize state (by
          rw [u32_usize nCount]
          exact h.next.denBound nCount.toNat hcountLt)
        let nSpa := nSpa.usetWord state.toUSize nCount (by
          rw [u32_usize state]
          exact h.next.spaBound state.toNat hs)
        let nCount' := nCount + 1
        have hnext : SetInv nDen nSpa nCount'.toNat nStates.toNat := by
          simp only [nDen, nSpa, nCount']
          exact SetInv.insertU32 h.next state hs hnot hcnt
        have hbuf : EvalBuf caps2 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
          simp only [caps2]
          split
          · have hbuf1 : EvalBuf caps1 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [caps1]
              split
              · exact h.buf.of_size (copyRow_size _ _ _ _ hw1.1 hstkW.1 hw1.2 hstkW.2) rfl
              · exact h.buf
            exact hbuf1.of_size (copyRow_size _ _ _ _ hnext1 hstk1 hnextW.2 hstkW.2) rfl
          · simp only [caps1]
            split
            · exact h.buf.of_size (copyRow_size _ _ _ _ hw1.1 hstkW.1 hw1.2 hstkW.2) rfl
            · exact h.buf
        have hno : ¬ sp' + 2 > stkS.size := by
          have := h.sp_le
          have := h.buf.stk_ge
          have := h.next.count_le
          omega
        have hnextLt : nextW.toNat < nStates.toNat := by
          simp only [nextW]
          rw [h.words.word_eq state hs 4 (Or.inl h4n) hoff4.1, h4n]
          exact h.words.next_lt state.toNat hs
        have hback : sp' + 1 = sp := by omega
        have hspEq : sp' = sp - 1 := by simp only [sp']
        have htop : sp' + 1 < stkS.size := by
          have := h.sp_le
          have := h.buf.stk_ge
          have := h.next.count_le
          omega
        have htop32 : sp' + 1 < 2 ^ 32 := by
          have := h.stack.sp_fit
          omega
        have hfit30 : sp + 1 ≤ 2 ^ 30 := by
          have hdiv : nStates.toNat ≤ 2 ^ 32 / 12 :=
            (Nat.le_div_iff_mul_le (by decide : 0 < 12)).mpr h.words.n_bytes
          have : 2 ^ 32 / 12 + 1 ≤ 2 ^ 30 := by decide
          have := h.sp_le
          have := hcountLt
          omega
        -- The live prefix never fills the buffer: `sp ≤ nCount + 1` and the stack
        -- was allocated with at least `n + 2` words. The check stays so the schedule
        -- is unchanged; the growing branch does not return.
        if hbad : sp' + 2 > stkS.size then
          False.elim (hno hbad)
        else
          have hwrite := h.stack.wordBound sp' (Nat.lt_of_lt_of_le hspLt h.stack.sp_le) hsp30
          have hstkSz (a : WordArray) (i : USize) (v : UInt32)
              (hb : (i * Regex.VM.Wide.wordBytes).toNat + 4 ≤ a.data.size) :
              (a.usetWord i v hb).size = a.size := by
            rw [WordArray.usetWord_eq]
            exact (WordArray.size_uset _ _ _ _).2
          if tag == tagEpsilon then
            let stk1 := stkS.usetWord sp'.toUSize nextW hwrite
            have hstack : StackInv stk1 (sp' + 1) nStates.toNat := by
              simp only [stk1]
              exact StackInv.cast
                (h.stack.succAt hspPos nextW hnextLt sp' hspEq hwrite) rfl hback
            have hbuf1 : EvalBuf caps2 stk1 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [stk1]
              exact hbuf.of_size rfl (hstkSz _ _ _ _)
            have hspLe : sp' + 1 ≤ nCount'.toNat + 1 := by
              rw [hback, toNat_u32_add_one hcnt]
              exact Nat.le_trans h.sp_le (Nat.le_succ _)
            have hcaps : CapsWf (s := s) caps2 nSlots (2 + 2 * nStates.toNat + stk1.size) := by
              simp only [stk1]
              rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
              exact hcaps2
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stk1 caps2 (sp' + 1) phase i sent :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf1, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, hcaps⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i ((sp - 1) + 1) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [show (sp - 1) + 1 = sp by omega, toNat_u32_add_one hcnt]
                exact fuel_keep hnotStep hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stk1 caps2 (sp' + 1)
              phase i h'
          else if hsplit : tag == tagSplit then
            have hextraLt : extra.toNat < nStates.toNat := by
              simp only [extra]
              rw [h.words.word_eq state hs 8 (Or.inr h8n) hoff8.1, h8n]
              exact h.words.split_lt state.toNat hs (by
                have htag : tag = wordAt words (12 * state.toNat) := by
                  simp only [tag, base]
                  exact h.words.tag_eq state hs htagB
                rw [← htag]
                exact (beq_iff_eq).mp hsplit)
            have hslot2 := h.buf.stackSlot (sp' + 1) htop htop32
            have htopW := h.buf.window (stackRow0 + (sp' + 1).toUSize)
              (2 + 2 * nStates.toNat + (sp' + 1)) hslot2.1 hslot2.2
            have htopDst :
                (rowOff (stackRow0 + (sp' + 1).toUSize) slots).toNat + slots.toNat * 8 ≤
                  caps2.size := by
              rw [hsz2]
              exact htopW.1
            have htopSrc : stkOff.toNat + slots.toNat * 8 ≤ caps2.size := by
              rw [hsz2]
              simp only [stkOff]
              exact hstkW.1
            let caps3 := copyRow caps2 (rowOff (stackRow0 + (sp' + 1).toUSize) slots) stkOff slots
              htopDst htopSrc htopW.2 hstkW.2
            have hcaps3 : CapsWf (s := s) caps3 nSlots (2 + 2 * nStates.toNat + stkS.size) := by
              simp only [caps3]
              exact CapsWf.copyRow hcaps2 (rowOff (stackRow0 + (sp' + 1).toUSize) slots) stkOff
                slots (2 + 2 * nStates.toNat + (sp' + 1)) (2 + 2 * nStates.toNat + sp')
                (h.buf.rowOff_eq (stackRow0 + (sp' + 1).toUSize)
                  (2 + 2 * nStates.toNat + (sp' + 1)) hslot2.1 hslot2.2)
                hsrcNat h.buf.slots_eq hslot2.2 hslot.2 htopDst htopSrc htopW.2 hstkW.2
            have hbuf3 : EvalBuf caps3 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat :=
              hbuf.of_size (copyRow_size _ _ _ _ htopDst htopSrc htopW.2 hstkW.2) rfl
            let stk1 := stkS.usetWord sp'.toUSize extra hwrite
            have hidx : (sp' + 1).toUSize = sp.toUSize := by
              apply USize.toNat_inj.mp
              rw [Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 htop32,
                Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (by
                  have := h.stack.sp_fit
                  omega : sp < 2 ^ 32)]
              exact hback
            have hpushB :
                ((sp' + 1).toUSize * Regex.VM.Wide.wordBytes).toNat + 4 ≤ stk1.data.size := by
              simp only [stk1]
              rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).1, hidx]
              exact h.stack.wordBound sp (by rw [← hback]; exact htop) (Nat.lt_of_succ_le hfit30)
            let stk2 := stk1.usetWord (sp' + 1).toUSize nextW hpushB
            have hstack : StackInv stk2 (sp' + 2) nStates.toNat := by
              have hnested := h.stack.splitAt hspPos (by rw [← hback]; exact htop) hfit30
                extra nextW hextraLt hnextLt sp' hspEq hwrite hpushB hidx
              simp only [stk2, stk1]
              exact StackInv.cast hnested rfl (by omega)
            have hbuf2 : EvalBuf caps3 stk2 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [stk2, stk1]
              exact hbuf3.of_size rfl (by
                rw [hstkSz (stkS.usetWord sp'.toUSize extra hwrite) (sp' + 1).toUSize nextW hpushB,
                  hstkSz stkS sp'.toUSize extra hwrite])
            have hspLe : sp' + 2 ≤ nCount'.toNat + 1 := by
              have h2 : sp' + 2 = sp + 1 := by omega
              rw [h2, toNat_u32_add_one hcnt]
              exact Nat.add_le_add_right h.sp_le 1
            have hcaps : CapsWf (s := s) caps3 nSlots (2 + 2 * nStates.toNat + stk2.size) := by
              simp only [stk2, stk1]
              rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2,
                WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
              exact hcaps3
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stk2 caps3 (sp' + 2) phase i sent :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf2, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, hcaps⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i ((sp - 1) + 2) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [show (sp - 1) + 2 = sp + 1 by omega, toNat_u32_add_one hcnt]
                exact fuel_split hnotStep hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stk2 caps3 (sp' + 2)
              phase i h'
          else if tag == tagSave then
            let caps3 :=
              if hex : extra.toNat < nSlots then
                uset caps2 (stkOff + extra.toUSize * slotBytes) (encodePos cp) (by
                  rw [hsz2]
                  simp only [stkOff]
                  exact h.buf.slotBound (stackRow0 + sp'.toUSize)
                    (2 + 2 * nStates.toNat + sp') hslot.1 hslot.2 extra hex)
              else
                caps2
            have hbuf3 : EvalBuf caps3 stkS slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [caps3]
              split
              · exact hbuf.of_size (uset_size _ _ _ _) rfl
              · exact hbuf
            have hcaps3 : CapsWf (s := s) caps3 nSlots (2 + 2 * nStates.toNat + stkS.size) := by
              simp only [caps3]
              split
              · rename_i hex
                have hoff := h.buf.slotOff_eq (stackRow0 + sp'.toUSize)
                  (2 + 2 * nStates.toNat + sp') hslot.1 hslot.2 extra hex
                have hb : (stkOff + extra.toUSize * slotBytes).toNat + 8 ≤ caps2.size := by
                  rw [hsz2]
                  simp only [stkOff]
                  exact h.buf.slotBound (stackRow0 + sp'.toUSize)
                    (2 + 2 * nStates.toNat + sp') hslot.1 hslot.2 extra hex
                have hwritten := CapsWf.writeSlot hcaps2
                  (stkOff + extra.toUSize * slotBytes) (encodePos cp)
                  (2 + 2 * nStates.toNat + sp') extra.toNat
                  (by simp only [stkOff]; exact hoff) hslot.2 hex
                  (SlotWord.of_pos cp h.hlen) hb
                exact uset_irrel caps2 (stkOff + extra.toUSize * slotBytes) (encodePos cp) hb
                  (by
                    rw [hsz2]
                    simp only [stkOff]
                    exact h.buf.slotBound (stackRow0 + sp'.toUSize)
                      (2 + 2 * nStates.toNat + sp') hslot.1 hslot.2 extra hex) ▸ hwritten
              · exact hcaps2
            let stk1 := stkS.usetWord sp'.toUSize nextW hwrite
            have hstack : StackInv stk1 (sp' + 1) nStates.toNat := by
              simp only [stk1]
              exact StackInv.cast
                (h.stack.succAt hspPos nextW hnextLt sp' hspEq hwrite) rfl hback
            have hbuf1 : EvalBuf caps3 stk1 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
              simp only [stk1]
              exact hbuf3.of_size rfl (hstkSz _ _ _ _)
            have hspLe : sp' + 1 ≤ nCount'.toNat + 1 := by
              rw [hback, toNat_u32_add_one hcnt]
              exact Nat.le_trans h.sp_le (Nat.le_succ _)
            have hcaps : CapsWf (s := s) caps3 nSlots (2 + 2 * nStates.toNat + stk1.size) := by
              simp only [stk1]
              rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
              exact hcaps3
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stk1 caps3 (sp' + 1) phase i sent :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf1, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, hcaps⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i ((sp - 1) + 1) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [show (sp - 1) + 1 = sp by omega, toNat_u32_add_one hcnt]
                exact fuel_keep hnotStep hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stk1 caps3 (sp' + 1)
              phase i h'
          else if tag == tagAnchor then
            if anchorTest extra cp then
              let stk1 := stkS.usetWord sp'.toUSize nextW hwrite
              have hstack : StackInv stk1 (sp' + 1) nStates.toNat := by
                simp only [stk1]
                exact StackInv.cast
                  (h.stack.succAt hspPos nextW hnextLt sp' hspEq hwrite) rfl hback
              have hbuf1 : EvalBuf caps2 stk1 slots cRow0 nRow0 stackRow0 nSlots nStates.toNat := by
                simp only [stk1]
                exact hbuf.of_size rfl (hstkSz _ _ _ _)
              have hspLe : sp' + 1 ≤ nCount'.toNat + 1 := by
                rw [hback, toNat_u32_add_one hcnt]
                exact Nat.le_trans h.sp_le (Nat.le_succ _)
              have hcaps : CapsWf (s := s) caps2 nSlots (2 + 2 * nStates.toNat + stk1.size) := by
                simp only [stk1]
                rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
                exact hcaps2
              have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                  p cp cCount cDen cSpa nCount' nDen nSpa stk1 caps2 (sp' + 1) phase i sent :=
                ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf1, h.i_le, hspLe,
                  h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, hcaps⟩
              have hlt : EvalRel
                  (evalMeasure p phase cCount i ((sp - 1) + 1) (nCount + 1).toNat nStates.toNat)
                  (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
                dec_fuel (by
                  rw [show (sp - 1) + 1 = sp by omega, toNat_u32_add_one hcnt]
                  exact fuel_keep hnotStep hcountLt)
              eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
                p cp matched clos
                cCount cDen cSpa
                nCount' nDen nSpa
                stk1 caps2 (sp' + 1)
                phase i h'
            else
              have hstack : StackInv stkS sp' nStates.toNat := by
                simpa [sp'] using h.stack.pop hspPos
              have hspLe : sp' ≤ nCount'.toNat + 1 := by
                rw [toNat_u32_add_one hcnt]
                exact Nat.le_trans (Nat.le_of_lt hspLt) (Nat.le_trans h.sp_le (Nat.le_succ _))
              have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                  p cp cCount cDen cSpa nCount' nDen nSpa stkS caps2 sp' phase i sent :=
                ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf, h.i_le, hspLe,
                  h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, hcaps2⟩
              have hlt : EvalRel
                  (evalMeasure p phase cCount i (sp - 1) (nCount + 1).toNat nStates.toNat)
                  (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
                dec_fuel (by
                  rw [toNat_u32_add_one hcnt]
                  exact fuel_discard hnotStep hspPos hcountLt)
              eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
                p cp matched clos
                cCount cDen cSpa
                nCount' nDen nSpa
                stkS caps2 sp'
                phase i h'
          else
            have hstack : StackInv stkS sp' nStates.toNat := by
              simpa [sp'] using h.stack.pop hspPos
            have hspLe : sp' ≤ nCount'.toNat + 1 := by
              rw [toNat_u32_add_one hcnt]
              exact Nat.le_trans (Nat.le_of_lt hspLt) (Nat.le_trans h.sp_le (Nat.le_succ _))
            have h' : RunInv words classes start nSlots nStates slots cRow0 nRow0 stackRow0
                p cp cCount cDen cSpa nCount' nDen nSpa stkS caps2 sp' phase i sent :=
              ⟨h.words, h.start_lt, h.curr, hnext, hstack, hbuf, h.i_le, hspLe,
                h.phase_ok, h.cp_rel, h.step_i, h.hlen, h.sentOk, hcaps2⟩
            have hlt : EvalRel
                (evalMeasure p phase cCount i (sp - 1) (nCount + 1).toNat nStates.toNat)
                (evalMeasure p phase cCount i sp nCount.toNat nStates.toNat) :=
              dec_fuel (by
                rw [toNat_u32_add_one hcnt]
                exact fuel_discard hnotStep hspPos hcountLt)
            eval words classes start nSlots nStates slots sent cRow0 nRow0 stackRow0
              p cp matched clos
              cCount cDen cSpa
              nCount' nDen nSpa
              stkS caps2 sp'
              phase i h'
termination_by evalMeasure p phase cCount i sp nCount.toNat nStates.toNat
decreasing_by
  all_goals
    unfold EvalRel at hlt
    exact hlt

def search {s : String} (nfa : FlatNFA) (scratch : Scratch) (sent : UInt64) (p : Pos s)
    (hwords : WordsWf nfa.words nfa.classes nfa.size.toNat)
    (hstart : nfa.start.toNat < nfa.size.toNat)
    (hscratch : ScratchInv (s := s) scratch)
    (hn : scratch.nStates.toNat = nfa.size.toNat)
    (hlen : s.utf8ByteSize + 1 < 2 ^ 64)
    (hsent : SlotWord s sent) :
    SearchRun (s := s) scratch.nSlots scratch.nStates :=
  if nfa.size == 0 then
    { matched := false, scratch, nSlots_eq := rfl, nStates_eq := rfl, inv := hscratch }
  else
    let slots := scratch.nSlots.toUSize
    let cRow0 : USize := 2
    let nRow0 : USize := 2 + scratch.nStates.toUSize
    let stackRow0 : USize := nRow0 + scratch.nStates.toUSize
    have hslots : slots.toNat = scratch.nSlots :=
      Regex.VM.Wide.toNat_toUSize_of_lt_2_pow_32 (ScratchInv.slots_lt hscratch)
    have hcRow : cRow0.toNat = 2 :=
      Regex.VM.Wide.toNat_uSize_ofNat_of_lt 2 (by decide)
    have hnU : scratch.nStates.toUSize.toNat = scratch.nStates.toNat :=
      UInt32.toNat_toUSize scratch.nStates
    have haddN : (2 : USize).toNat + scratch.nStates.toUSize.toNat < 2 ^ 32 := by
      rw [Regex.VM.Wide.toNat_uSize_ofNat_of_lt 2 (by decide), hnU]
      have := WordsWf.le_30 (hn.symm ▸ hwords)
      omega
    have hnRow : nRow0.toNat = 2 + scratch.nStates.toNat := by
      rw [show nRow0 = (2 : USize) + scratch.nStates.toUSize from rfl,
        toNat_add_of_lt_2_pow_32 haddN,
        Regex.VM.Wide.toNat_uSize_ofNat_of_lt 2 (by decide), hnU]
    have haddS : nRow0.toNat + scratch.nStates.toUSize.toNat < 2 ^ 32 := by
      rw [hnRow, hnU]
      have := WordsWf.le_30 (hn.symm ▸ hwords)
      omega
    have hstkRow : stackRow0.toNat = 2 + 2 * scratch.nStates.toNat := by
      rw [show stackRow0 = nRow0 + scratch.nStates.toUSize from rfl,
        toNat_add_of_lt_2_pow_32 haddS, hnRow, hnU]
      omega
    have hne : cRow0.toNat ≠ nRow0.toNat := by
      rw [hcRow, hnRow]
      intro heq
      have hz : scratch.nStates.toNat = 0 := by omega
      rw [hn] at hz
      exact (Nat.ne_of_lt hwords.n_pos).symm hz
    have hbuf0 : EvalBuf scratch.caps scratch.stkS slots cRow0 nRow0 stackRow0
        scratch.nSlots scratch.nStates.toNat :=
      { slots_eq := hslots
        c_row := Or.inl hcRow
        n_row := Or.inr hnRow
        rows_ne := hne
        stack_row := hstkRow
        stk_ge := hscratch.stk_ge
        rows_size := hscratch.rows_size
        rows_fit := hscratch.rows_fit }
    have hroom : 0 < scratch.stkS.size := by
      have := hscratch.stk_ge
      omega
    have hrowLt : 2 + 2 * scratch.nStates.toNat <
        2 + 2 * scratch.nStates.toNat + scratch.stkS.size := by
      have := hscratch.stk_ge
      omega
    have hw := hbuf0.window stackRow0 (2 + 2 * scratch.nStates.toNat)
      (Or.inr hbuf0.stack_row) hrowLt
    let caps := fillRow scratch.caps (rowOff stackRow0 slots) slots sent hw.1 hw.2
    let stkS := scratch.stkS.usetWord 0 nfa.start
      (hscratch.stack.wordBound 0 hroom (by decide))
    have hstack : StackInv stkS 1 scratch.nStates.toNat := by
      simp only [stkS]
      exact hscratch.stack.reset hroom nfa.start (hn.symm ▸ hstart)
    have hbuf : EvalBuf caps stkS slots cRow0 nRow0 stackRow0 scratch.nSlots
        scratch.nStates.toNat := by
      simp only [caps, stkS]
      exact (hbuf0.of_size (fillRow_size _ _ _ _ hw.1 hw.2) rfl).of_size rfl (by
        rw [WordArray.usetWord_eq]
        exact (WordArray.size_uset _ _ _ _).2)
    have hcaps : CapsWf (s := s) caps scratch.nSlots
        (2 + 2 * scratch.nStates.toNat + stkS.size) := by
      simp only [caps, stkS]
      rw [WordArray.usetWord_eq, (WordArray.size_uset _ _ _ _).2]
      exact CapsWf.fillAt hscratch.caps hbuf0 rfl stackRow0 (2 + 2 * scratch.nStates.toNat)
        (Or.inr hbuf0.stack_row) hrowLt sent hsent hw.1 hw.2
    have hz : (0 : UInt32).toNat = 0 :=
      UInt32.toNat_ofNat_of_lt (by decide : 0 < UInt32.size)
    have h' : RunInv nfa.words nfa.classes nfa.start scratch.nSlots scratch.nStates slots
        cRow0 nRow0 stackRow0 p p (0 : UInt32) scratch.cDen scratch.cSpa
        (0 : UInt32) scratch.nDen scratch.nSpa stkS caps 1 phaseClosure 0 sent :=
      ⟨hn.symm ▸ hwords, hn.symm ▸ hstart, hscratch.curr, hscratch.next, hstack, hbuf,
        by rw [hz]; exact Nat.zero_le _,
        by rw [hz]; exact Nat.le_refl _,
        Or.inl rfl, CpRel.closure p,
        fun hc => absurd hc (by decide : phaseClosure ≠ phaseStepClosure),
        hlen, hsent, hcaps⟩
    eval nfa.words nfa.classes nfa.start scratch.nSlots scratch.nStates slots sent
      cRow0 nRow0 stackRow0
      p p false false
      (0 : UInt32) scratch.cDen scratch.cSpa
      (0 : UInt32) scratch.nDen scratch.nSpa
      stkS caps 1
      phaseClosure 0 h'

def captureNextBuf {s : String} (nfa : NFA) (wf : nfa.WellFormed) (flat : FlatNFA)
    (hflat : ofNFA nfa = some flat) (bufferSize : Nat)
    (hlayout : layoutOk nfa.size bufferSize)
    (hlen : s.utf8ByteSize + 1 < 2 ^ 64) (p : Pos s) :
    Option (Buffer s bufferSize) :=
  let scratch := Scratch.mkFor nfa.size bufferSize
  have hscratch : ScratchInv (s := s) scratch := ScratchInv.ofMkFor nfa.size bufferSize hlayout
  have hwords := WordsWf.ofNFA wf hflat
  have hstart : flat.start.toNat < flat.size.toNat := by
    have spec := ofNFA_spec hflat
    rw [spec.2.2.2.1, spec.2.2.2.2.1]
    exact wf.start_lt
  have hn : scratch.nStates.toNat = flat.size.toNat := by
    have spec := ofNFA_spec hflat
    have hn32 : nfa.size < UInt32.size := spec.2.1
    simp only [scratch, Scratch.mkFor]
    rw [toNat_toUInt32_of_lt hn32, spec.2.2.2.1]
  have hslots : scratch.nSlots = bufferSize := by
    simp only [scratch, Scratch.mkFor]
  let run := search flat scratch (sentinelWord s) p hwords hstart hscratch hn hlen
    (SlotWord.sentinel hlen)
  if run.matched then
    have hrows : 0 < 2 + 2 * run.scratch.nStates.toNat + run.scratch.stkS.size := by
      have := run.inv.stk_ge
      omega
    let buf := toBuffer run.scratch.caps run.scratch.nSlots
      (fun i => CapsWf.row0Bound run.inv.caps hrows i)
      (fun i => CapsWf.row0Word run.inv.caps hrows i)
    have hnS : run.scratch.nSlots = bufferSize := run.nSlots_eq.trans hslots
    some (hnS ▸ buf)
  else
    none

/-- All non-overlapping matches, using the same empty-match advance as `Regex.Matches.next?`. -/
def findAll.go (flat : FlatNFA) (info : OptimizationInfo) (haystack : String)
    (hlen : haystack.utf8ByteSize + 1 < 2 ^ 64)
    (hwords : WordsWf flat.words flat.classes flat.size.toNat)
    (hstart : flat.start.toNat < flat.size.toNat)
    (sent : UInt64) (hsent : SlotWord haystack sent)
    (pos : PosPlusOne haystack) (accum : Array Slice) (scratch : Scratch)
    (hscratch : ScratchInv (s := haystack) scratch)
    (hn : scratch.nStates.toNat = flat.size.toNat)
    (h2 : scratch.nSlots = 2) : Array Slice :=
  if h : pos.isValid then
    let start := info.findStart (pos.asPos h)
    let run := search flat scratch sent start hwords hstart hscratch hn hlen hsent
    if run.matched then
      have hrows : 0 < 2 + 2 * run.scratch.nStates.toNat + run.scratch.stkS.size := by
        have := run.inv.stk_ge
        omega
      have hn2 : run.scratch.nSlots = 2 := by rw [run.nSlots_eq]; exact h2
      have hb0 := CapsWf.slot0Bound run.inv.caps hrows (by rw [hn2]; decide)
      have hb1 := CapsWf.slot1Bound run.inv.caps hrows (by rw [hn2]; decide)
      let startPos := decode (uget run.scratch.caps 0 hb0)
        (CapsWf.slot0Word run.inv.caps hrows (by rw [hn2]; decide) hb0)
      let stopPos := decode (uget run.scratch.caps slotBytes hb1)
        (CapsWf.slot1Word run.inv.caps hrows (by rw [hn2]; decide) hb1)
      if hv : stopPos.isValid = true ∧ startPos ≤ stopPos then
        have isStopPosValid : stopPos.isValid := hv.1
        have h' : startPos.isValid := PosPlusOne.isValid_of_isValid_of_le isStopPosValid hv.2
        have hle : (startPos.asPos h').offset ≤ (stopPos.asPos isStopPosValid).offset := by
          simpa [PosPlusOne.asPos_def] using (PosPlusOne.le_iff.mp hv.2)
        let slice : Slice :=
          ⟨haystack, startPos.asPos h', stopPos.asPos isStopPosValid, String.Pos.le_iff.mpr hle⟩
        let nextPos := PosPlusOne.pos (stopPos.asPos isStopPosValid)
        let scratch' := run.scratch
        have hscratch' : ScratchInv (s := haystack) scratch' := run.inv
        have hn' : scratch'.nStates.toNat = flat.size.toNat := by
          rw [show scratch'.nStates = run.scratch.nStates from rfl, run.nStates_eq]
          exact hn
        have h2' : scratch'.nSlots = 2 := by
          rw [show scratch'.nSlots = run.scratch.nSlots from rfl, run.nSlots_eq]
          exact h2
        if hlt : pos < nextPos then
          have hdec : nextPos.remainingBytes < pos.remainingBytes :=
            (PosPlusOne.lt_iff_remainingBytes_lt).mp hlt
          findAll.go flat info haystack hlen hwords hstart sent hsent nextPos
            (accum.push slice) scratch' hscratch' hn' h2'
        else
          have hdec : (pos.next h).remainingBytes < pos.remainingBytes :=
            (PosPlusOne.lt_iff_remainingBytes_lt).mp (PosPlusOne.lt_next pos h)
          findAll.go flat info haystack hlen hwords hstart sent hsent (pos.next h)
            (accum.push slice) scratch' hscratch' hn' h2'
      else
        accum
    else
      accum
  else
    accum
termination_by pos.remainingBytes
decreasing_by
  all_goals
    exact hdec

def findAll (nfa : NFA) (wf : nfa.WellFormed) (flat : FlatNFA)
    (hflat : ofNFA nfa = some flat) (info : OptimizationInfo) (haystack : String)
    (hlayout : layoutOk nfa.size 2)
    (hlen : haystack.utf8ByteSize + 1 < 2 ^ 64) : Array Slice :=
  let scratch := Scratch.mkFor nfa.size 2
  have hscratch : ScratchInv (s := haystack) scratch :=
    ScratchInv.ofMkFor nfa.size 2 hlayout
  have hwords := WordsWf.ofNFA wf hflat
  have hstart : flat.start.toNat < flat.size.toNat := by
    have spec := ofNFA_spec hflat
    rw [spec.2.2.2.1, spec.2.2.2.2.1]
    exact wf.start_lt
  have hn : scratch.nStates.toNat = flat.size.toNat := by
    have spec := ofNFA_spec hflat
    have hn32 : nfa.size < UInt32.size := spec.2.1
    simp only [scratch, Scratch.mkFor]
    rw [toNat_toUInt32_of_lt hn32, spec.2.2.2.1]
  have h2 : scratch.nSlots = 2 := by
    simp only [scratch, Scratch.mkFor]
  findAll.go flat info haystack hlen hwords hstart (sentinelWord haystack)
    (SlotWord.sentinel hlen) haystack.startPosPlusOne #[] scratch hscratch hn h2

def count (nfa : NFA) (wf : nfa.WellFormed) (flat : FlatNFA)
    (hflat : ofNFA nfa = some flat) (info : OptimizationInfo) (haystack : String)
    (hlayout : layoutOk nfa.size 2)
    (hlen : haystack.utf8ByteSize + 1 < 2 ^ 64) : Nat :=
  (findAll nfa wf flat hflat info haystack hlayout hlen).size

def byteSpans (slices : Array Slice) : Array (Nat × Nat) :=
  slices.map fun s => (s.startInclusive.offset.byteIdx, s.endExclusive.offset.byteIdx)

/-- Byte offsets of a capture buffer. Proof fields are not compared. -/
def bufferOffsets {s : String} {n : Nat} (b : Buffer s n) : List Nat :=
  List.ofFn fun i : Fin n => (b[i]).offset.byteIdx

/--
Compare capture slots against the stock `BufferStrategy` at every position.
`none` means every slot offset agrees.
-/
def buffersAgree.go {haystack : String} (pattern : String) (re : Regex) (flat : FlatNFA)
    (bufSize : Nat) (hflat : ofNFA re.nfa = some flat)
    (hlayout : layoutOk re.nfa.size bufSize)
    (hlen : haystack.utf8ByteSize + 1 < 2 ^ 64)
    (pos : PosPlusOne haystack) : Option String :=
  if h : pos.isValid then
    let p := pos.asPos h
    let stock := re.captureNextBuf bufSize p
    let refined := captureNextBuf re.nfa re.wf flat hflat bufSize hlayout hlen
      (re.optimizationInfo.findStart p)
    let same :=
      match stock, refined with
      | none, none => true
      | some a, some b => bufferOffsets a == bufferOffsets b
      | _, _ => false
    if same then
      buffersAgree.go pattern re flat bufSize hflat hlayout hlen (pos.next h)
    else
      some s!"buffer mismatch /{pattern}/ at {p.offset.byteIdx}"
  else
    none
termination_by pos.remainingBytes
decreasing_by
  exact (PosPlusOne.lt_iff_remainingBytes_lt).mp (PosPlusOne.lt_next pos h)

def buffersAgree (pattern haystack : String) : Option String :=
  let re := Regex.parse! pattern
  match hflat : ofNFA re.nfa with
  | none => some s!"flat conversion failed for /{pattern}/"
  | some flat =>
    if hlen : haystack.utf8ByteSize + 1 < 2 ^ 64 then
      if hlayout : layoutOk re.nfa.size (re.maxTag + 1) then
        buffersAgree.go pattern re flat (re.maxTag + 1) hflat hlayout hlen
          haystack.startPosPlusOne
      else
        some s!"capture layout does not fit for /{pattern}/"
    else
      some s!"haystack does not fit in a capture word for /{pattern}/"

/-- Compare match spans against the stock VM. `none` means they agree. -/
def mismatch? (pattern haystack : String) : Option String :=
  let re := Regex.parse! pattern
  match hflat : ofNFA re.nfa with
  | none => some s!"flat conversion failed for /{pattern}/"
  | some flat =>
    if hlen : haystack.utf8ByteSize + 1 < 2 ^ 64 then
      if hlayout : layoutOk re.nfa.size 2 then
        let vm := byteSpans (re.findAll haystack)
        let fl := byteSpans (findAll re.nfa re.wf flat hflat re.optimizationInfo haystack
          hlayout hlen)
        if vm == fl then
          none
        else
          some s!"mismatch /{pattern}/ on {haystack}: vm={vm} refined={fl}"
      else
        some s!"capture layout does not fit for /{pattern}/"
    else
      some s!"haystack does not fit in a capture word for /{pattern}/"

def selfCheck : Array String :=
  let cases : Array (String × String) := #[
    ("", ""),
    ("", "abc"),
    ("a", "a"),
    ("a", "b"),
    ("a*", ""),
    ("a*", "aaa"),
    ("a*", "baaac"),
    ("a+", "baaac"),
    ("a?", "a"),
    ("a?", ""),
    ("a|b", "ababa"),
    ("bool|boolean", "boolean"),
    ("a|ab", "ab"),
    ("(a+)(b*)", "aaabb"),
    ("(a+)(b*)|(c+)", "a aa aab c cc"),
    ("\\d{4}-\\d{2}-\\d{2}", "2025-05-24: x\n2025-05-26: y"),
    (".*", "abc\ndef"),
    ("^a", "a\na"),
    ("a$", "ba\na"),
    ("\\bword\\b", "a word wordy word"),
    ("\\b\\w+\\b", "pre café word 漢字 _x"),
    ("\\B\\w", "abcあ_"),
    ("[a-z]+", "AbCdefGHI"),
    ("[^A-Za-z]+", "aあb漢c"),
    ("[あ-ん]+", "アあいうア"),
    ("\\w", "あa_"),
    (".", "あ\nb"),
    ("[0-9]+", "id 42 and 7"),
    ("\\w+", "foo_bar baz"),
    ("a{2,4}", "aaaaaaaa"),
    ("(ab)+", "abababxab"),
    ("(a|aa)*", "aaaa"),
    ("(a*)*", "aaa"),
    ("a*", "bbbb"),
    (".", "é"),
    ("é+", "aéééb")
  ]
  cases.filterMap fun (pat, hay) => mismatch? pat hay <|> buffersAgree pat hay

end Regex.VM.Refined

end
