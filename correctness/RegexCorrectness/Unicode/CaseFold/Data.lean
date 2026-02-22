import Regex.Unicode.CaseFold

namespace Regex.Unicode

set_option autoImplicit false

/--
Generic pair-wise decision procedure over `Fin n`.

Intended usage: for concrete inputs, discharge goals of the form `checkAllPairs f = true` with `by native_decide`.
This runs the Boolean search using native evaluation (fast for small tables), but relies on the compiler/runtime
rather than kernel normalization. The resulting fact is then consumed by `checkAllPairs_spec` to obtain kernel-checked
statements about `caseFoldRepresentatives.get`.
-/
def checkAllPairs {n : Nat} (f : Fin n → Fin n → Bool) : Bool :=
  let rec go₂ (i : Nat) (hi : i ≤ n) (j : Fin n) : Bool :=
    if _ : i ≥ n then true else
    f ⟨i, by grind⟩ j && go₂ (i + 1) (by grind) j
  let rec go₁ (j : Nat) (hj : j ≤ n) : Bool :=
    if _ : j ≥ n then true else
    go₂ 0 (by grind) ⟨j, by grind⟩ && go₁ (j + 1) (by grind)
  go₁ 0 (by grind)

theorem checkAllPairs_spec {n : Nat} {f : Fin n → Fin n → Bool} (hcheck : checkAllPairs f = true) (i j : Fin n) :
  f i j = true := by
  have h₂ (i : Nat) (hi : i ≤ n) (j : Fin n) (h : checkAllPairs.go₂ f i hi j = true) : ∀ k : Fin n, i ≤ k.val → f k j = true := by
    fun_induction checkAllPairs.go₂ f i hi j <;> grind
  have h₂' (j : Fin n) (h : checkAllPairs.go₂ f 0 (by grind) j = true) : ∀ k : Fin n, f k j = true := by
    grind [h₂ 0 (by grind) j h]
  have h₁ (j : Nat) (hj : j ≤ n) (h : checkAllPairs.go₁ f j hj = true) :  ∀ i k : Fin n, j ≤ k.val → f i k = true := by
    fun_induction checkAllPairs.go₁ f j hj <;> grind

  exact h₁ 0 (by grind) hcheck i j (by grind)

def isLtFirst (arr : Array (Char × Char)) (i j : Fin arr.size) : Bool :=
  decide (i < j → arr[i].1 < arr[j].1)

theorem sorted_of_checkAllPairs_isLtFirst {arr : Array (Char × Char)} (hcheck : checkAllPairs (isLtFirst arr) = true)
  (i j : Fin arr.size) (h : i < j) :
  arr[i].1 < arr[j].1 := by
  have := checkAllPairs_spec hcheck i j
  grind [isLtFirst]

theorem checkAllPairs_isLtFirst_caseFoldRepresentatives : checkAllPairs (isLtFirst caseFoldRepresentatives.get) = true := by
  native_decide

theorem caseFoldRepresentatives_sorted : ∀ i j : Fin caseFoldRepresentatives.get.size, i < j → caseFoldRepresentatives.get[i].1 < caseFoldRepresentatives.get[j].1 := by
  intro i j h
  grind [sorted_of_checkAllPairs_isLtFirst, checkAllPairs_isLtFirst_caseFoldRepresentatives]

def noChain (arr : Array (Char × Char)) (i j : Fin arr.size) : Bool :=
  decide (arr[i].1 ≠ arr[j].2)

theorem no_chain_of_checkAllPairs_noChain {arr : Array (Char × Char)} (hcheck : checkAllPairs (noChain arr) = true)
  (i j : Fin arr.size) :
  arr[i].1 ≠ arr[j].2 := by
  have := checkAllPairs_spec hcheck i j
  grind [noChain]

theorem checkAllPairs_noChain_caseFoldRepresentatives : checkAllPairs (noChain caseFoldRepresentatives.get) = true := by
  native_decide

theorem caseFoldRepresentatives_no_chain (p₁ p₂ : Char × Char) (h₁ : p₁ ∈ caseFoldRepresentatives.get) (h₂ : p₂ ∈ caseFoldRepresentatives.get) :
  p₁.1 ≠ p₂.2 := by
  rw [Array.mem_iff_getElem] at h₁ h₂
  obtain ⟨i₁, h₁, eq₁⟩ := h₁
  obtain ⟨i₂, h₂, eq₂⟩ := h₂
  simpa [eq₁, eq₂] using no_chain_of_checkAllPairs_noChain checkAllPairs_noChain_caseFoldRepresentatives ⟨i₁, h₁⟩ ⟨i₂, h₂⟩

end Regex.Unicode
