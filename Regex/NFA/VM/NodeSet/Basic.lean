import Regex.Lemmas
import Std.Data.Fin.Lemmas
import Std.Data.Array.Lemmas

namespace NFA.VM

-- Deprecated.
def NodeSet (n : Nat) := { array : Array Bool // array.size = n }

def NodeSet.empty {n : Nat} : NodeSet n :=
  ⟨mkArray n false, by simp⟩

def NodeSet.get (ns : NodeSet n) (i : Fin n) : Bool :=
  ns.val.get (i.cast ns.property.symm)

instance : GetElem (NodeSet n) Nat Bool (fun _ i => i < n) where
  getElem ns i h := ns.get ⟨i, h⟩

def NodeSet.set (ns : NodeSet n) (i : Fin n) : NodeSet n :=
  ⟨ns.val.set (i.cast ns.property.symm) true, by simp [ns.property]⟩

def NodeSet.unset (ns : NodeSet n) (i : Fin n) : NodeSet n :=
  ⟨ns.val.set (i.cast  ns.property.symm) false, by simp [ns.property]⟩

@[simp]
theorem NodeSet.get_unset_eq (ns : NodeSet n) (i : Fin n) :
  (ns.unset i).get i = false := by
  simp [NodeSet.get, NodeSet.unset]
  rw [Array.get_set]
  . simp
  . simp [ns.property]

theorem NodeSet.get_unset_ne (ns : NodeSet n) (i j : Fin n) (ne : i.val ≠ j.val) :
  (ns.unset i).get j = ns.get j := by
  simp [NodeSet.get, NodeSet.unset]
  rw [Array.get_set]
  . simp [ne]
  . simp [ns.property, ne]

def NodeSet.count_set (ns : NodeSet n) : Nat :=
  go ns 0 0 (Nat.zero_le _)
where
  go (ns : NodeSet n) (accum : Nat) (i : Nat) (hle : i ≤ n) : Nat :=
    if h : i = n then
      accum
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      let accum := if ns.get ⟨i, hlt⟩ then accum + 1 else accum
      go ns accum (i + 1) hlt
  termination_by n - i

def NodeSet.count_unset (ns : NodeSet n) : Nat :=
  go ns 0 0 (Nat.zero_le _)
where
  go (ns : NodeSet n) (accum : Nat) (i : Nat) (hle : i ≤ n) : Nat :=
    if h : i = n then
      accum
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      let accum := if ns.get ⟨i, hlt⟩ then accum else accum + 1
      go ns accum (i + 1) hlt
  termination_by n - i

def NodeSet.clear (ns : NodeSet n) : NodeSet n :=
  go ns 0 (Nat.zero_le _)
where
  go (ns : NodeSet n) (i : Nat) (hle : i ≤ n) : NodeSet n :=
    if h : i = n then
      ns
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      go (ns.unset ⟨i, hlt⟩) (i + 1) hlt
  termination_by n - i

-- NOTE: this should overwrite to ns₁ if it's unique
def NodeSet.merge (ns₁ ns₂ : NodeSet n) : NodeSet n :=
  go ns₁ ns₂ 0 (Nat.zero_le _)
where
  go (ns₁ ns₂ : NodeSet n) (i : Nat) (hle : i ≤ n) : NodeSet n :=
    if h : i = n then
      ns₁
    else
      have hlt : i < n := Nat.lt_of_le_of_ne hle h
      let ns₁ := if ns₂.get ⟨i, hlt⟩ then ns₁.set ⟨i, hlt⟩ else ns₁
      go ns₁ ns₂ (i + 1) hlt
  termination_by n - i

end NFA.VM
