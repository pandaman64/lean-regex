import Std.Data.Array.Lemmas

namespace NFA.VM

def Vec (α : Type) (n : Nat) := { a : Array α // a.size = n }

def Vec.fromArray {α : Type} (a : Array α) : Vec α a.size := ⟨a, rfl⟩

def Vec.get (v : Vec α n) (i : Nat) (h : i < n) : α :=
  v.val[i]'(by simp [v.property, h])

instance : GetElem (Vec α n) Nat α (fun _ i => i < n) where
  getElem := Vec.get

def Vec.set (v : Vec α n) (i : Nat) (h : i < n) (a : α) : Vec α n :=
  ⟨v.val.set ⟨i, by simp [v.property, h]⟩ a, by simp [v.property]⟩

@[simp]
theorem Vec.get_set_eq (v : Vec α n) (h : i < n) :
  (v.set i h a)[i] = a := by
  simp [Vec.set, getElem]
  unfold Vec.get
  simp
  rw [Array.get_set_eq]

@[simp]
theorem Vec.get_set_ne (v : Vec α n) (h₁ : i < n) (h₂ : j < n) (ne : i ≠ j) :
  (v.set i h₁ a)[j] = v[j] := by
  simp [Vec.set, getElem]
  unfold Vec.get
  simp
  rw [Array.get_set_ne]
  assumption

theorem Vec.get_set (v : Vec α n) (h₁ : i < n) (h₂ : j < n) :
  (v.set i h₁ a)[j] = if i = j then a else v[j] := by
  if h : i = j then
    subst j
    simp
  else
    simp [h]

theorem Vec.set_set (v : Vec α n) (h : i < n) :
  (v.set i h a).set i h b = v.set i h b := by
  apply Subtype.eq
  simp [Vec.set]
  rw [Array.set_set]

end NFA.VM
