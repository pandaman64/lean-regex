import Regex.Lemmas
import Regex.NFA.Basic

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

/--
  Extend the ordering to εNFA.
-/
def NFA.le (nfa₁ nfa₂ : NFA) : Prop :=
  ∀ i : Nat, (h₁ : i < nfa₁.nodes.size) → ∃ h₂ : i < nfa₂.nodes.size, nfa₁[i] ≤ nfa₂[i]

instance : LE NFA where
  le := NFA.le

theorem NFA.le_size_of_le {nfa₁ nfa₂ : NFA} (h : nfa₁ ≤ nfa₂) : nfa₁.nodes.size ≤ nfa₂.nodes.size :=
  match Nat.lt_or_ge nfa₂.nodes.size nfa₁.nodes.size with
  | .inr le => le
  | .inl gt => nomatch Nat.lt_irrefl _ (h nfa₂.nodes.size gt).1

theorem NFA.le_rfl {nfa : NFA} : nfa ≤ nfa
  | _, h => ⟨h, Node.le_rfl⟩

theorem NFA.le_trans {nfa₁ nfa₂ nfa₃ : NFA} : nfa₁ ≤ nfa₂ → nfa₂ ≤ nfa₃ → nfa₁ ≤ nfa₃ := by
  intro h₁ h₂ i h
  have : nfa₁.nodes.size ≤ nfa₃.nodes.size := Nat.le_trans (NFA.le_size_of_le h₁) (NFA.le_size_of_le h₂)
  have h' : i < nfa₃.nodes.size := Nat.lt_of_lt_of_le h this
  have h'' : nfa₁[i] ≤ nfa₃[i] := Node.le_trans (h₁ i h).2 (h₂ i (h₁ i h).1).2
  exact ⟨h', h''⟩

theorem NFA.le_of_eq {nfa₁ nfa₂ : NFA} : nfa₁ = nfa₂ → nfa₁ ≤ nfa₂ := fun h => h ▸ NFA.le_rfl

def _instLENFA : LE NFA := inferInstance
instance : Trans NFA.le NFA.le NFA.le := ⟨NFA.le_trans⟩
instance : Trans _instLENFA.le _instLENFA.le _instLENFA.le := ⟨NFA.le_trans⟩

instance : Preorder NFA where
  le_refl := @NFA.le_rfl
  le_trans := @NFA.le_trans

end NFA
