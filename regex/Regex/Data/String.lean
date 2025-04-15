namespace Char

theorem default_utf8Size : (default : Char).utf8Size = 1 := rfl

end Char

namespace String

theorem utf8GetAux_not_valid (cs : List Char) (i p : Pos) (nv : ¬Pos.isValid.go p cs i) : utf8GetAux cs i p = default := by
  induction cs generalizing i with
  | nil => simp [utf8GetAux]
  | cons c cs ih =>
    simp [Pos.isValid.go] at nv
    simp [utf8GetAux, nv.1]
    exact ih (i + c) (by simp [nv.2])

theorem get_not_valid (s : String) (p : Pos) (nv : ¬p.isValid s) : s.get p = default := by
  simp [get]
  exact utf8GetAux_not_valid s.data 0 p nv

theorem next_not_valid (s : String) (p : Pos) (nv : ¬p.isValid s) : s.next p = p + ⟨1⟩ := by
  simp [next, get_not_valid s p nv]
  rfl

theorem next_le_endPos_not_valid (s : String) (p : Pos) (lt : p < s.endPos) (nv : ¬p.isValid s) : s.next p ≤ s.endPos := by
  have : p.byteIdx < s.endPos.byteIdx := lt
  have : s.next p = p + ⟨1⟩ := next_not_valid s p nv
  have : (s.next p).byteIdx = p.byteIdx + 1 := by
    simp [this]
  show (s.next p).byteIdx ≤ s.endPos.byteIdx
  omega

-- From Batteries
private theorem utf8GetAux_of_valid (cs cs' : List Char) {i p : Nat} (hp : i + utf8ByteSize.go cs = p) :
    utf8GetAux (cs ++ cs') ⟨i⟩ ⟨p⟩ = cs'.headD default := by
  match cs, cs' with
  | [], [] => rfl
  | [], c::cs' => simp [← hp, utf8GetAux, utf8ByteSize.go]
  | c::cs, cs' =>
    simp only [List.cons_append, utf8GetAux, Char.reduceDefault]
    rw [if_neg]
    case hnc =>
      simp only [← hp, utf8ByteSize.go, Pos.ext_iff]
      have : c.utf8Size > 0 := Char.utf8Size_pos c
      omega
    refine utf8GetAux_of_valid cs cs' ?_
    simpa [Nat.add_assoc, Nat.add_comm, utf8ByteSize.go] using hp

-- From Batteries
private theorem get_of_valid (cs cs' : List Char) : get ⟨cs ++ cs'⟩ ⟨utf8ByteSize.go cs⟩ = cs'.headD default :=
  utf8GetAux_of_valid _ _ (Nat.zero_add _)

@[simp]
theorem utf8Size.go_append (cs₁ cs₂ : List Char) : utf8ByteSize.go (cs₁ ++ cs₂) = utf8ByteSize.go cs₁ + utf8ByteSize.go cs₂ := by
  induction cs₁ with
  | nil => simp [utf8ByteSize.go]
  | cons c cs₁ ih =>
    simp [utf8ByteSize.go, ih]
    omega

@[simp]
theorem utf8Size.go_nil : utf8ByteSize.go [] = 0 := rfl

@[simp]
theorem utf8Size.go_cons (c : Char) (cs : List Char) : utf8ByteSize.go (c :: cs) = utf8ByteSize.go cs + c.utf8Size := by
  simp [utf8ByteSize.go]

@[simp]
theorem utf8Size.go_singleton (c : Char) : utf8ByteSize.go [c] = c.utf8Size := by simp

private theorem split_of_valid' (cs₁ cs₂ : List Char) (p : Pos) (v : Pos.isValid.go p cs₂ ⟨utf8ByteSize.go cs₁⟩) :
  ∃ cs₁' cs₂', cs₁ ++ cs₂ = cs₁' ++ cs₂' ∧ p = ⟨utf8ByteSize.go cs₁'⟩ := by
  induction cs₂ generalizing cs₁ with
  | nil =>
    simp [Pos.isValid.go] at v
    exact ⟨cs₁, [], rfl, by simp [←v]⟩
  | cons c cs₂ ih =>
    simp [Pos.isValid.go] at v
    cases v with
    | inl eq => exact ⟨cs₁, c :: cs₂, rfl, by simp [←eq]⟩
    | inr v =>
      have ⟨cs₁', cs₂', seq⟩ := ih (cs₁ ++ [c]) (by simp; exact v)
      simp at seq
      exact ⟨cs₁', cs₂', seq⟩

private theorem split_of_valid (s : String) (p : Pos) (v : p.isValid s) : ∃ cs₁ cs₂, s = ⟨cs₁ ++ cs₂⟩ ∧ p = ⟨utf8ByteSize.go cs₁⟩ := by
  have ⟨cs₁, cs₂, seq, eq⟩ := split_of_valid' [] s.data p v
  simp at seq
  exact ⟨cs₁, cs₂, by simp [String.ext_iff, seq], eq⟩

private theorem split_of_valid_lt (s : String) (p : Pos) (v : p.isValid s) (lt : p < s.endPos) : ∃ cs₁ c cs₂, s = ⟨cs₁ ++ c :: cs₂⟩ ∧ p = ⟨utf8ByteSize.go cs₁⟩ := by
  have ⟨cs₁, cs₂, seq, eq⟩ := split_of_valid' [] s.data p v
  simp at seq
  match cs₂ with
  | [] =>
    simp at seq
    simp [←seq] at eq
    simp [eq, endPos, utf8ByteSize] at lt
  | c :: cs₂ => exact ⟨cs₁, c, cs₂, by simp [String.ext_iff, seq], eq⟩

theorem next_le_endPos_valid (s : String) (p : Pos) (v : p.isValid s) (lt : p < s.endPos) : s.next p ≤ s.endPos := by
  have ⟨cs₁, c, cs₂, seq, eq⟩ := split_of_valid_lt s p v lt
  have := get_of_valid cs₁ (c :: cs₂)
  subst s p
  simp [next, this, endPos, utf8ByteSize]
  show utf8ByteSize.go cs₁ + c.utf8Size ≤ utf8ByteSize.go cs₁ + (utf8ByteSize.go cs₂ + c.utf8Size)
  omega

theorem next_le_endPos (s : String) (p : Pos) (lt : p < s.endPos) : s.next p ≤ s.endPos := by
  match v : p.isValid s with
  | true => exact next_le_endPos_valid s p v lt
  | false => exact next_le_endPos_not_valid s p lt (by simp [v])

end String

namespace String.Iterator

theorem next'_eq_next (it : Iterator) (h : it.hasNext) : it.next' h = it.next := by
  simp [next', next]

theorem next_toString (it : Iterator) : it.next.toString = it.toString := by
  simp [next, toString]

theorem next_le_endPos (it : Iterator) (h : it.hasNext) : (it.next' h).pos ≤ (it.next' h).toString.endPos := by
  have lt : it.pos < it.toString.endPos := by
    simp [hasNext] at h
    exact h
  simp [next'_eq_next, next_toString]
  exact String.next_le_endPos it.toString it.pos lt

theorem lt_next (it : Iterator) : it.pos < it.next.pos := by
  simp [pos, next]
  exact String.lt_next _ _

@[simp]
theorem next'_remainingBytes_lt {it : Iterator} {h : it.hasNext} : (it.next' h).remainingBytes < it.remainingBytes := by
  simp [hasNext] at h
  simp [next', remainingBytes, String.next]
  have : (it.s.get it.i).utf8Size > 0 := Char.utf8Size_pos _
  omega

end String.Iterator
