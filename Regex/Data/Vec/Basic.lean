import Batteries.Data.Array.Lemmas

namespace Regex.Data

-- TODO: migrate to Std Vector. It has necessary lemmas in master as of Dec 2024, but it's not released yet.
def Vec (α : Type) (n : Nat) := { a : Array α // a.size = n }

instance [Repr α] : Repr (Vec α n) := inferInstanceAs (Repr { a : Array α // a.size = n })
instance [ToString α] : ToString (Vec α n) := inferInstanceAs (ToString { a : Array α // a.size = n })

def Vec.mk {α : Type} (a : Array α) : Vec α a.size := ⟨a, rfl⟩

def Vec.mk' {α : Type} {n : Nat} (a : Array α) (h : a.size = n) : Vec α n := ⟨a, h⟩

def Vec.ofFn {α : Type} {n : Nat} (f : Fin n → α) : Vec α n :=
  ⟨Array.ofFn f, by simp⟩

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

end Regex.Data
