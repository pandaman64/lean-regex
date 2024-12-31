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
    simp [h]
  else
    simp [h]

theorem Vec.set_set (v : Vec α n) (h : i < n) :
  (v.set i h a).set i h b = v.set i h b := by
  apply Subtype.eq
  simp [Vec.set]
  rw [Array.set_set]

def Vec.setIfInBounds (v : Vec α n) (i : Nat) (a : α) : Vec α n :=
  if h : i < n then v.set i h a else v

@[simp]
theorem Vec.get_setIfInBounds_eq (v : Vec α n) (h : i < n) :
  (v.setIfInBounds i a)[i] = a := by
  simp [Vec.setIfInBounds, h]

@[simp]
theorem Vec.get_setIfInBounds_ne (v : Vec α n) (h : j < n) (ne : i ≠ j) :
  (v.setIfInBounds i a)[j] = v[j] := by
  simp [Vec.setIfInBounds]
  split <;> simp [ne]

theorem Vec.get_setIfInBounds (v : Vec α n) (h : j < n) :
  (v.setIfInBounds i a)[j] = if i = j then a else v[j] := by
  if h : i = j then
    simp [h]
  else
    simp [h]

theorem Vec.ext {v₁ v₂ : Vec α n} (eq : ∀ (i : Nat) (h : i < n), v₁[i] = v₂[i]) : v₁ = v₂ := by
  apply Subtype.eq
  simp [Array.ext_iff, v₁.property, v₂.property]
  intro i h _
  exact eq i h

theorem Vec.ext_iff {v₁ v₂ : Vec α n} :
  v₁ = v₂ ↔ ∀ (i : Nat) (h : i < n), v₁[i] = v₂[i] :=
  ⟨fun eq => by simp [eq], Vec.ext⟩

end Regex.Data
