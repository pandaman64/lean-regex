-- Minimal theory about the bijection between `Fin n`.
module

namespace Regex.Data.SparseSet.Bijection

open Function (Injective Surjective)

/-- An injective endofunction on `Fin n` is surjective.

`grind` panics on the natural proof of this fact in Lean v4.36.0
(`Unknown constant _inhabitedExprDummy` in `Lean.Meta.Grind.mkCongrDefaultProof`),
so the argument is spelled out directly. -/
public theorem surj_of_inj {n} (f : Fin n → Fin n) (hf : Injective f) : Surjective f := by
  induction n with
  | zero =>
    intro y
    exact y.elim0
  | succ n ih =>
    let n' : Fin (n + 1) := Fin.last n
    let f' (x : Fin n) : Fin n :=
      if hy : (f x.castSucc).val < n then
        ⟨(f x.castSucc).val, hy⟩
      else
        ⟨(f n').val, by
          have hyeq : (f x.castSucc).val = n := by
            have := (f x.castSucc).isLt
            omega
          have hne : f n' ≠ f x.castSucc := by
            intro heq
            have : n'.val = (x.castSucc).val := congrArg Fin.val (hf heq)
            simp [n', Fin.last, Fin.castSucc] at this
            omega
          have hneq : (f n').val ≠ n := by
            intro hv
            exact hne (Fin.ext (by rw [hyeq, hv]))
          have := (f n').isLt
          omega⟩
    have inj' : Injective f' := by
      intro a b heq
      by_cases ha : (f a.castSucc).val < n <;> by_cases hb : (f b.castSucc).val < n
      · have hfa : f' a = ⟨(f a.castSucc).val, ha⟩ := by simp [f', ha]
        have hfb : f' b = ⟨(f b.castSucc).val, hb⟩ := by simp [f', hb]
        have hval : (f a.castSucc).val = (f b.castSucc).val := by
          have := congrArg Fin.val (hfa.symm.trans (heq.trans hfb))
          simpa using this
        have : a.castSucc = b.castSucc := hf (Fin.ext hval)
        exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val this)
      · have hfa : f' a = ⟨(f a.castSucc).val, ha⟩ := by simp [f', ha]
        have hfb : f' b = ⟨(f n').val, by
            have := (f b.castSucc).isLt
            have hb' : (f b.castSucc).val = n := by omega
            have hne : f n' ≠ f b.castSucc := by
              intro heq'
              have : n'.val = (b.castSucc).val := congrArg Fin.val (hf heq')
              simp [n', Fin.last, Fin.castSucc] at this
              omega
            have hneq : (f n').val ≠ n := by
              intro hv
              exact hne (Fin.ext (by rw [hb', hv]))
            have := (f n').isLt
            omega⟩ := by simp [f', hb]
        have hval : (f a.castSucc).val = (f n').val := by
          have := congrArg Fin.val (hfa.symm.trans (heq.trans hfb))
          simpa using this
        have : a.castSucc = n' := hf (Fin.ext hval)
        have : a.val = n := by simpa [n', Fin.last, Fin.castSucc] using congrArg Fin.val this
        omega
      · have hfa : f' a = ⟨(f n').val, by
            have := (f a.castSucc).isLt
            have ha' : (f a.castSucc).val = n := by omega
            have hne : f n' ≠ f a.castSucc := by
              intro heq'
              have : n'.val = (a.castSucc).val := congrArg Fin.val (hf heq')
              simp [n', Fin.last, Fin.castSucc] at this
              omega
            have hneq : (f n').val ≠ n := by
              intro hv
              exact hne (Fin.ext (by rw [ha', hv]))
            have := (f n').isLt
            omega⟩ := by simp [f', ha]
        have hfb : f' b = ⟨(f b.castSucc).val, hb⟩ := by simp [f', hb]
        have hval : (f n').val = (f b.castSucc).val := by
          have := congrArg Fin.val (hfa.symm.trans (heq.trans hfb))
          simpa using this
        have : n' = b.castSucc := hf (Fin.ext hval)
        have : n = b.val := by simpa [n', Fin.last, Fin.castSucc] using congrArg Fin.val this
        omega
      · have ha' : f a.castSucc = n' := by
          apply Fin.ext
          have := (f a.castSucc).isLt
          simp [n', Fin.last]
          omega
        have hb' : f b.castSucc = n' := by
          apply Fin.ext
          have := (f b.castSucc).isLt
          simp [n', Fin.last]
          omega
        have : a.castSucc = b.castSucc := hf (ha'.trans hb'.symm)
        exact Fin.ext (by simpa [Fin.castSucc] using congrArg Fin.val this)
    have surj' : Surjective f' := ih f' inj'
    intro y
    have yle : y.val ≤ n := Nat.le_of_lt_succ y.isLt
    rcases Nat.lt_or_eq_of_le yle with hlt | heq
    · obtain ⟨x, hx⟩ := surj' ⟨y.val, hlt⟩
      by_cases hfx : (f x.castSucc).val < n
      · have hx' : f' x = ⟨(f x.castSucc).val, hfx⟩ := by simp [f', hfx]
        have hval : (f x.castSucc).val = y.val := by
          have := congrArg Fin.val (hx'.symm.trans hx)
          simpa using this
        exact ⟨x.castSucc, Fin.ext hval⟩
      · have hbound : (f n').val < n := by
          have := (f x.castSucc).isLt
          have hxeq : (f x.castSucc).val = n := by omega
          have hne : f n' ≠ f x.castSucc := by
            intro heq'
            have : n'.val = (x.castSucc).val := congrArg Fin.val (hf heq')
            simp [n', Fin.last, Fin.castSucc] at this
            omega
          have hneq : (f n').val ≠ n := by
            intro hv
            exact hne (Fin.ext (by rw [hxeq, hv]))
          have := (f n').isLt
          omega
        have hx' : f' x = ⟨(f n').val, hbound⟩ := by simp [f', hfx]
        have hval : (f n').val = y.val := by
          have := congrArg Fin.val (hx'.symm.trans hx)
          simpa using this
        exact ⟨n', Fin.ext hval⟩
    · by_cases hfn : (f n').val < n
      · obtain ⟨x, hx⟩ := surj' ⟨(f n').val, hfn⟩
        have hnot : ¬ (f x.castSucc).val < n := by
          intro hltx
          have hx' : f' x = ⟨(f x.castSucc).val, hltx⟩ := by simp [f', hltx]
          have hval : (f x.castSucc).val = (f n').val := by
            have := congrArg Fin.val (hx'.symm.trans hx)
            simpa using this
          have : x.castSucc = n' := hf (Fin.ext hval)
          have : x.val = n := by simpa [n', Fin.last, Fin.castSucc] using congrArg Fin.val this
          omega
        have hxe : (f x.castSucc).val = n := by
          have := (f x.castSucc).isLt
          omega
        exact ⟨x.castSucc, Fin.ext (by simp [hxe, heq])⟩
      · have hfn' : (f n').val = n := by
          have := (f n').isLt
          omega
        exact ⟨n', Fin.ext (by simp [heq, hfn'])⟩

end Regex.Data.SparseSet.Bijection
