import RegexCorrectness.Lemmas
import RegexCorrectness.NFA.Basic

namespace NFA

/--
  We define n₁ ≤ n₂ when the transition of n₁ is a subset of that of n₂.
-/
def Node.le (n₁ n₂ : Node) : Prop :=
  n₁.charStep ≤ n₂.charStep ∧ n₁.εStep ≤ n₂.εStep

instance : LE Node where
  le := Node.le

theorem Node.le_spec {n₁ n₂ : Node} :
  n₁ ≤ n₂ ↔ (∀c, n₁.charStep c ⊆ n₂.charStep c) ∧ n₁.εStep ⊆ n₂.εStep := by rfl

theorem Node.le_rfl {n : Node} : n ≤ n := ⟨fun _ => subset_rfl, subset_rfl⟩

theorem Node.le_trans {n₁ n₂ n₃ : Node} : n₁ ≤ n₂ → n₂ ≤ n₃ → n₁ ≤ n₃ := by
  intro h₁ h₂
  exact ⟨Trans.trans h₁.left h₂.left, Trans.trans h₁.right h₂.right⟩

theorem Node.le_of_eq {n₁ n₂ : Node} : n₁ = n₂ → n₁ ≤ n₂ := fun h => h ▸ Node.le_rfl

def _instLENode : LE Node := inferInstance
instance : Trans Node.le Node.le Node.le := ⟨Node.le_trans⟩
instance : Trans _instLENode.le _instLENode.le _instLENode.le := ⟨Node.le_trans⟩

instance : Preorder Node where
  le_refl := @Node.le_rfl
  le_trans := @Node.le_trans

@[simp]
theorem Node.minimal_fail {n : Node} : .fail ≤ n :=
  ⟨fun _ => Set.empty_subset _, Set.empty_subset _⟩

/--
  Extend the ordering to εNFA.
-/
def le (nfa₁ nfa₂ : NFA) : Prop :=
  ∀ i : Fin nfa₁.nodes.size, ∃ h₂ : i < nfa₂.nodes.size, nfa₁[i.val] ≤ nfa₂[i.val]

instance : LE NFA where
  le := le

theorem le_size_of_le {nfa₁ nfa₂ : NFA} (h : nfa₁ ≤ nfa₂) : nfa₁.nodes.size ≤ nfa₂.nodes.size :=
  match Nat.lt_or_ge nfa₂.nodes.size nfa₁.nodes.size with
  | .inr le => le
  | .inl gt => nomatch Nat.lt_irrefl _ (h ⟨nfa₂.nodes.size, gt⟩).1

theorem le_refl {nfa : NFA} : nfa ≤ nfa
  | i => ⟨i.isLt, Node.le_rfl⟩

theorem le_trans {nfa₁ nfa₂ nfa₃ : NFA} (h₁ : nfa₁ ≤ nfa₂) (h₂ : nfa₂ ≤ nfa₃) : nfa₁ ≤ nfa₃ := by
  intro i
  have lt₂ : i < nfa₂.nodes.size := Nat.lt_of_lt_of_le i.isLt (le_size_of_le h₁)
  have lt₃ : i < nfa₃.nodes.size := Nat.lt_of_lt_of_le lt₂ (le_size_of_le h₂)
  have le : nfa₁[i] ≤ nfa₃[i] := Node.le_trans (h₁ i).2 (h₂ ⟨i.val, lt₂⟩).2
  exact ⟨lt₃, le⟩

def _instLENFA : LE NFA := inferInstance
instance : Trans NFA.le NFA.le NFA.le := ⟨NFA.le_trans⟩
instance : Trans _instLENFA.le _instLENFA.le _instLENFA.le := ⟨NFA.le_trans⟩

instance : Preorder NFA where
  le_refl := @NFA.le_refl
  le_trans := @NFA.le_trans

end NFA
