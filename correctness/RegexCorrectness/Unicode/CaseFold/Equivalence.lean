import RegexCorrectness.Unicode.CaseFold.BinarySearch
import RegexCorrectness.Unicode.CaseFold.Data
import Mathlib.Tactic.SplitIfs

namespace Regex.Unicode

/--
Characterization of `getCaseFoldEquivChars` when a representative character is found.
-/
theorem getCaseFoldEquivChars_found {c : Char} (i : Fin caseFoldRepresentatives.get.size)
  (h : caseFoldRepresentatives.get[i].1 = c) :
  haveI : caseFoldRepresentatives.get[i].2 ∈ caseFoldInvMap.get := (mem_buildCaseFoldInvMap_iff.mpr (by grind : (caseFoldRepresentatives.get[i].1, caseFoldRepresentatives.get[i].2) ∈ caseFoldRepresentatives.get)).1
  getCaseFoldEquivChars c = (caseFoldRepresentatives.get[i].2, caseFoldInvMap.get[caseFoldRepresentatives.get[i].2]) := by
  unfold getCaseFoldEquivChars
  have bsEq := binarySearch_of_mem c caseFoldRepresentatives.get (·.1) caseFoldRepresentatives_sorted ⟨i, by grind⟩ (by grind)
  dsimp [Fin.getElem_fin] at h
  simp [bsEq, h]

/--
Characterization of `getCaseFoldEquivChars` when no representative character is found.
-/
theorem getCaseFoldEquivChars_not_found {c : Char}
  (h : ¬∃ i : Fin caseFoldRepresentatives.get.size, caseFoldRepresentatives.get[i].1 = c) :
  getCaseFoldEquivChars c = (c, caseFoldInvMap.get[c]?.getD #[]) := by
  unfold getCaseFoldEquivChars
  dsimp
  split_ifs
  next lt eq => exact (h ⟨⟨binarySearch c caseFoldRepresentatives.get (·.1), lt⟩, eq⟩).elim
  all_goals simp

/-- Two characters are case-fold equivalent if one is in the case-fold equivalence class of the other. -/
def CaseFoldEquiv (c₁ c₂ : Char) : Prop :=
  c₂ = (getCaseFoldEquivChars c₁).1 ∨ c₂ ∈ (getCaseFoldEquivChars c₁).2

/-- Alternative definition of case-fold equivalence with a trivial equivalence proof. -/
def CaseFoldEquiv' (c₁ c₂ : Char) : Prop :=
  getCaseFoldEquivChars c₁ = getCaseFoldEquivChars c₂

instance instCaseFoldEquivEquivalence' : Equivalence CaseFoldEquiv' where
  refl := by grind [CaseFoldEquiv']
  symm := by grind [CaseFoldEquiv']
  trans := by grind [CaseFoldEquiv']

theorem caseFoldEquiv'_iff_caseFoldEquiv {c₁ c₂ : Char} : CaseFoldEquiv' c₁ c₂ ↔ CaseFoldEquiv c₁ c₂ := by
  refine Iff.intro ?_ ?_
  . unfold CaseFoldEquiv' CaseFoldEquiv
    intro eq
    simp only [eq]
    if hfound : ∃ i : Fin caseFoldRepresentatives.get.size, caseFoldRepresentatives.get[i].1 = c₂ then
      obtain ⟨i, hfound⟩ := hfound
      simp only [getCaseFoldEquivChars_found i hfound, Fin.getElem_fin]
      exact .inr (mem_buildCaseFoldInvMap_iff.mpr (by grind : (c₂, caseFoldRepresentatives.get[i].2) ∈ caseFoldRepresentatives.get)).2
    else
      simp [getCaseFoldEquivChars_not_found hfound]
  . intro h
    if hfound₁ : ∃ i : Fin caseFoldRepresentatives.get.size, caseFoldRepresentatives.get[i].1 = c₁ then
      let ⟨i₁, eq₁⟩ := hfound₁
      simp only [CaseFoldEquiv, getCaseFoldEquivChars_found i₁ eq₁, Fin.getElem_fin] at h
      cases h with
      | inl eq =>
        -- c₂ is the representative character for the equivalence class of c₁, so no entry for c₂ itself.
        have hfound₂ : ¬∃ i : Fin caseFoldRepresentatives.get.size, caseFoldRepresentatives.get[i].1 = c₂ := by
          grind [caseFoldRepresentatives_no_chain]
        have mem : c₂ ∈ caseFoldInvMap.get := by
          have := mem_caseFoldInvMap_iff.mpr (by grind : (c₁, c₂) ∈ caseFoldRepresentatives.get)
          grind
        simp [CaseFoldEquiv', getCaseFoldEquivChars_found i₁ eq₁, getCaseFoldEquivChars_not_found hfound₂, ←eq, mem]
      | inr mem =>
        -- c₂ is another character that maps to the same representative character as c₁.
        have mem' : (c₂, caseFoldRepresentatives.get[i₁.val].2) ∈ caseFoldRepresentatives.get := mem_caseFoldInvMap_iff.mp ⟨_, mem⟩
        rw [Array.mem_iff_getElem] at mem'
        obtain ⟨i₂, hi₂, eq₂⟩ := mem'
        simp [CaseFoldEquiv', getCaseFoldEquivChars_found i₁ eq₁,
          getCaseFoldEquivChars_found ⟨i₂, hi₂⟩ (by grind : caseFoldRepresentatives.get[i₂].1 = c₂), eq₂]
    else
      simp only [CaseFoldEquiv, getCaseFoldEquivChars_not_found hfound₁] at h
      cases h with
      | inl eq =>
        -- c₁ = c₂
        grind [CaseFoldEquiv']
      | inr mem =>
      -- c₁ is the representative character for the equivalence class of c₂.
        if mem₁ : c₁ ∈ caseFoldInvMap.get then
          simp [mem₁] at mem
          have mem' := mem_caseFoldInvMap_iff.mp ⟨mem₁, mem⟩
          rw [Array.mem_iff_getElem] at mem'
          obtain ⟨j, hj, eq⟩ := mem'
          simp [CaseFoldEquiv', getCaseFoldEquivChars_not_found hfound₁,
            getCaseFoldEquivChars_found ⟨j, hj⟩ (by grind : caseFoldRepresentatives.get[j].1 = c₂), eq, mem₁]
        else
          simp [mem₁] at mem

theorem caseFoldEquiv'_eq_caseFoldEquiv : CaseFoldEquiv' = CaseFoldEquiv := by
  grind [caseFoldEquiv'_iff_caseFoldEquiv]

instance instCaseFoldEquivEquivalence : Equivalence CaseFoldEquiv :=
  caseFoldEquiv'_eq_caseFoldEquiv ▸ instCaseFoldEquivEquivalence'


-- Due to the dependence on `native_decide` in `Data.lean`, the proof has `Lean.trustCompiler` as an axiom.
/--
info: 'Regex.Unicode.instCaseFoldEquivEquivalence' depends on axioms: [propext,
 Classical.choice,
 Lean.ofReduceBool,
 Lean.trustCompiler,
 Quot.sound]
-/
#guard_msgs in
#print axioms instCaseFoldEquivEquivalence

end Regex.Unicode
