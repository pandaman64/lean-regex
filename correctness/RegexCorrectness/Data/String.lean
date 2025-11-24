import Batteries.Data.String
import Mathlib.Tactic.Common
import Regex.Data.String

namespace String.Iterator

theorem ext {it₁ it₂ : Iterator} (hs : it₁.s = it₂.s) (hi : it₁.i = it₂.i) : it₁ = it₂ :=
  show ⟨it₁.s, it₁.i⟩ = it₂ from hs ▸ hi ▸ rfl

theorem ext_iff {it₁ it₂ : Iterator} : it₁ = it₂ ↔ it₁.s = it₂.s ∧ it₁.i = it₂.i :=
  ⟨fun h => ⟨h ▸ rfl, h ▸ rfl⟩, fun ⟨hs, hi⟩ => ext hs hi⟩

theorem hasNext_of_not_atEnd {it : Iterator} (h : ¬it.atEnd) : it.hasNext := by
  simp [hasNext, atEnd] at *
  exact h

@[simp]
theorem ne_next (it : Iterator) : it ≠ it.next := by
  simp [ext_iff, next, Pos.Raw.ext_iff]
  exact Nat.ne_of_lt (lt_next it)

@[simp]
theorem next_ne (it : Iterator) : it.next ≠ it := it.ne_next.symm

theorem nextn_next_eq_next_nextn (it : Iterator) (n : Nat) : (it.nextn n).next = it.next.nextn n := by
  induction n generalizing it with
  | zero => simp [nextn]
  | succ n ih => simp [nextn, ih it.next]

end String.Iterator

namespace String

theorem eq_of_append_utf8Len {cs₁ cs₂ cs₃ cs₄ : List Char}
  (h₁ : cs₁ ++ cs₂ = cs₃ ++ cs₄) (h₂ : utf8Len cs₁ = utf8Len cs₃) :
  cs₁ = cs₃ ∧ cs₂ = cs₄ := by
  induction cs₁ generalizing cs₃ with
  | nil =>
    have := String.utf8Len_eq_zero.mp h₂.symm
    simp_all
  | cons c cs₁' ih =>
    cases cs₃ with
    | nil =>
      simp at h₂
      have := Char.utf8Size_pos c
      omega
    | cons c' cs₃' =>
      simp at h₁
      simp [h₁] at h₂
      have := ih h₁.2 h₂
      simp [h₁, this]

theorem eq_of_append_eq (l mr lm r : List Char) (le : utf8Len l ≤ utf8Len lm) (eq : l ++ mr = lm ++ r) :
  ∃ m, mr = m ++ r ∧ lm = l ++ m := by
  induction l generalizing lm with
  | nil => exact ⟨lm, by simpa using eq, by simp⟩
  | cons c l ih =>
    match lm with
    | [] =>
      simp at le
      have : c.utf8Size > 0 := Char.utf8Size_pos c
      omega
    | c' :: lm =>
      simp at eq
      simp [eq] at le
      have ⟨m, eq₁, eq₂⟩ := ih lm le eq.2
      exact ⟨m, eq₁, by simp [eq, eq₂]⟩

end String

namespace String.Iterator.Valid

theorem next' {it : Iterator} (v : it.Valid) (h : ¬it.atEnd) : it.next.Valid := by
  apply v.next
  simp [hasNext, atEnd] at *
  exact h

theorem validFor_of_valid_pos_le {it it' : Iterator} (v : it.Valid) (v' : it'.Valid) (eqs : it.toString = it'.toString) (le : it.pos ≤ it'.pos) :
  ∃ (l m r : List Char), it.ValidFor l.reverse (m ++ r) ∧ it'.ValidFor (m.reverse ++ l.reverse) r := by
  have ⟨lrev, mr, vf⟩ := v.validFor
  have ⟨lmrev, r, vf'⟩ := v'.validFor

  have hstring : it.toString = String.mk (lrev.reverse ++ mr) := by simpa using vf.toString
  have hstring' : it'.toString = String.mk (lmrev.reverse ++ r) := by simpa using vf'.toString
  have eq : lrev.reverse ++ mr = lmrev.reverse ++ r := by
    rw [hstring, hstring', String.mk_eq_asString, String.mk_eq_asString] at eqs
    exact List.asString_injective eqs

  have hpos : it.pos = ⟨utf8Len lrev⟩ := vf.pos
  have hpos' : it'.pos = ⟨utf8Len lmrev⟩ := vf'.pos
  have le' : utf8Len lrev.reverse ≤ utf8Len lmrev.reverse := by
    rw [hpos, hpos'] at le
    simpa using le

  have ⟨m, eq₁, eq₂⟩ := String.eq_of_append_eq lrev.reverse mr lmrev.reverse r le' eq
  have eq₂ : lmrev = m.reverse ++ lrev :=
    calc lmrev
      _ = lmrev.reverse.reverse := by simp
      _ = (lrev.reverse ++ m).reverse := by rw [eq₂]
      _ = m.reverse ++ lrev := by simp

  exact ⟨lrev.reverse, m, r, by simpa [←eq₁] using vf, by simpa [←eq₂] using vf'⟩

theorem valid_pos_le_of_validFor {it it' : Iterator} {l m r : List Char} (vf₁ : it.ValidFor l.reverse (m ++ r)) (vf₂ : it'.ValidFor (m.reverse ++ l.reverse) r) :
  it.toString = it'.toString ∧ it.pos ≤ it'.pos :=
  ⟨by simp [vf₁.toString, vf₂.toString], by simp [vf₁.pos, vf₂.pos]⟩

theorem pos_le_or_ge_next {it it' : Iterator} (v : it.Valid) (v' : it'.Valid) (eqs : it.toString = it'.toString) :
  it.pos ≤ it'.pos ∨ it'.next.pos ≤ it.pos := by
  if h : it.pos ≤ it'.pos then
    exact .inl h
  else
    have lt : it'.pos < it.pos := Nat.lt_of_not_ge h
    have ⟨l, m, r, vf', vf⟩ := validFor_of_valid_pos_le v' v eqs.symm (Nat.le_of_lt lt)
    match m with
    | [] =>
      simp at vf vf'
      have eq : it.pos = it'.pos := by
        simp [vf.pos, vf'.pos]
      exact .inl (eq ▸ Nat.le_refl _)
    | c :: m =>
      have vf' := vf'.next
      simp at vf vf'
      have le : it'.next.pos ≤ it.pos := by
        simp [vf.pos, vf'.pos]
      exact .inr le

theorem validFor_of_hasNext {it : Iterator} (h : it.hasNext) (v : it.Valid) :
  ∃ l r, it.ValidFor l (it.curr :: r) := by
  have ⟨l, r, vf⟩ := v.validFor
  match r with
  | [] => simp [vf.hasNext] at h
  | c :: r => exact ⟨l, r, by simpa [vf.curr] using vf⟩

end String.Iterator.Valid

namespace String.Iterator.ValidFor

theorem eq {it : Iterator} {l₁ r₁ l₂ r₂} (v₁ : it.ValidFor l₁ r₁) (v₂ : it.ValidFor l₂ r₂) :
  l₁ = l₂ ∧ r₁ = r₂ := by
  have o₁ := v₁.out'
  have o₂ := v₂.out'
  simp [o₁, String.ext_iff, Pos.Raw.ext_iff] at o₂
  have := String.eq_of_append_utf8Len o₂.1 (by simp [o₂.2])
  simpa

theorem eq_it {it₁ it₂ : Iterator} {l r} (v₁ : it₁.ValidFor l r) (v₂ : it₂.ValidFor l r) : it₁ = it₂ := by
  simp [Iterator.ext_iff, v₁.toString, v₂.toString, v₁.pos, v₂.pos]

theorem exists_cons_of_not_atEnd {l r} {it : Iterator} (v : it.ValidFor l r) (h : ¬it.atEnd) :
  ∃ r', r = it.curr :: r' := by
  have := v.atEnd
  simp [h] at this
  have ⟨c, r', heq⟩ := List.exists_cons_of_ne_nil this
  subst heq
  have := v.curr
  simp at this
  subst this
  exact ⟨r', rfl⟩

theorem pos_atEnd {l} {it : Iterator} (v : it.ValidFor l []) : it.pos = it.toString.endPos := by
  simp [v.out']

end String.Iterator.ValidFor

namespace String.Iterator

theorem eq_of_valid_of_next_eq {it₁ it₂ : Iterator} (v₁ : it₁.Valid) (v₂ : it₂.Valid) (h : it₁.next = it₂.next) : it₁ = it₂ := by
  have eqs₁₂ : it₁.toString = it₂.toString := by
    have : it₁.next.toString = it₂.next.toString := by rw [h]
    simpa [Iterator.next_toString] using this
  have ⟨l₁, r₁, vf₁⟩ := v₁.validFor
  have ⟨l₂, r₂, vf₂⟩ := v₂.validFor
  match r₁, r₂ with
  | [], [] =>
    have eqs₁ : it₁.toString = String.mk (l₁.reverse) := vf₁.toString
    have eqs₂ : it₂.toString = String.mk (l₂.reverse) := vf₂.toString
    have eqs : l₁ = l₂ := by
      rw [eqs₁, eqs₂, String.mk_eq_asString, String.mk_eq_asString] at eqs₁₂
      exact List.reverse_inj.mp (List.asString_injective eqs₁₂)
    exact vf₁.eq_it (eqs ▸ vf₂)
  | c₁ :: r₁, c₂ :: r₂ =>
    have vf₁' := vf₁.next
    have vf₂' := vf₂.next
    have eq := vf₁'.eq (h ▸ vf₂')
    simp at eq
    simp [eq] at vf₁
    exact vf₁.eq_it vf₂
  | [], c₂ :: r₂ =>
    have pos₁ : it₁.pos = it₁.toString.endPos := vf₁.pos_atEnd
    have pos₂ : it₂.next.pos ≤ it₂.toString.endPos := vf₂.next.valid.le_endPos
    rw [←eqs₁₂, ←h, ←pos₁] at pos₂
    exact ((Nat.not_le_of_lt it₁.lt_next) pos₂).elim
  | c₁ :: r₁, [] =>
    have pos₁ : it₁.next.pos ≤ it₁.toString.endPos := vf₁.next.valid.le_endPos
    have pos₂ : it₂.pos = it₂.toString.endPos := vf₂.pos_atEnd
    rw [eqs₁₂, h, ←pos₂] at pos₁
    exact ((Nat.not_le_of_lt it₂.lt_next) pos₁).elim

@[grind =]
theorem find_toString {it : Iterator} {p : Char → Bool} : (it.find p).toString = it.toString := by
  fun_induction find it p <;> grind [Iterator.next_toString]

theorem find_le_pos {it : Iterator} {p : Char → Bool} : it.pos ≤ (it.find p).pos := by
  fun_induction find it p
  next => exact Nat.le_refl _
  next => exact Nat.le_refl _
  next it _ _ ih => exact Nat.le_trans (Nat.le_of_lt it.lt_next) ih

theorem find_soundness (it it' : Iterator) (p : Char → Bool) (h : it' = it.find p) : (¬it'.atEnd ∧ p it'.curr) ∨ it'.atEnd := by
  revert h
  fun_induction find it p <;> grind

theorem find_valid_of_valid {it : Iterator} {p : Char → Bool} (v : it.Valid) : (it.find p).Valid := by
  fun_induction find it p
  next => grind
  next => grind
  next it atEnd _ ih => exact ih (v.next (hasNext_of_not_atEnd atEnd))

theorem find_completenessAux (it it' : Iterator) {p : Char → Bool} {l r : List Char} (vf : it.ValidFor l r) (h : it' = it.find p) :
  ∃ m r', it'.ValidFor (m ++ l) r' ∧ ∀ c ∈ m, ¬p c := by
  revert h
  fun_induction find it p generalizing l r
  next it atEnd =>
    intro eq
    subst it'
    exact ⟨[], r, vf, by simp⟩
  next it atEnd h =>
    intro eq
    subst it'
    exact ⟨[], r, vf, by simp⟩
  next it atEnd h ih =>
    match r with
    | [] => simp [vf.atEnd] at atEnd
    | c :: r =>
      intro eq
      have ⟨m, r', vf', h'⟩ := ih vf.next eq
      refine ⟨m ++ [c], r', by simp [vf'], fun c' mem => ?_⟩
      simp at mem
      cases mem with
      | inl mem => exact h' c' mem
      | inr eq => simpa [eq, vf.curr] using h

theorem find_completeness {it : Iterator} {p : Char → Bool} (v : it.Valid) (it' : Iterator) (v' : it'.Valid)
  (eqs : it'.toString = it.toString) (ge : it.pos ≤ it'.pos) (lt : it'.pos < (it.find p).pos) :
  ¬p it'.curr := by
  have ⟨l, m, r, vf₁, vf₂⟩ := Valid.validFor_of_valid_pos_le v v' eqs.symm ge
  have ⟨m', r', vf₃, h⟩ := find_completenessAux it (it.find p) vf₁ rfl
  have eqcs : l ++ m ++ r = l ++ m'.reverse ++ r' := by
    have eqs₁ : it.toString = String.mk (l ++ m ++ r) := by simpa using vf₁.toString
    have eqs₂ : (it.find p).toString = String.mk (l ++ m'.reverse ++ r') := by simpa using vf₃.toString
    rw [find_toString, eqs₁, String.mk_eq_asString, String.mk_eq_asString] at eqs₂
    exact List.asString_injective eqs₂
  simp at eqcs
  have ltLen : utf8Len m < utf8Len m' := by
    have eqp₁ : it'.pos = ⟨utf8Len m + utf8Len l⟩ := by simpa using vf₂.pos
    have eqp₂ : (it.find p).pos = ⟨utf8Len m' + utf8Len l⟩ := by simpa using vf₃.pos
    rw [eqp₁, eqp₂] at lt
    simpa using lt
  have ⟨mr, eq₁, eq₂⟩ := String.eq_of_append_eq m r m'.reverse r' (by simpa using Nat.le_of_lt ltLen) eqcs
  match r with
  | [] =>
    simp at eqcs
    have : utf8Len m = utf8Len m' + utf8Len r' := by simp [eqcs]
    grind
  | c :: r =>
    match mr with
    | [] =>
      simp at eq₁
      simp [eq₁] at eqcs
      simp [eqcs] at ltLen
    | c' :: mr =>
      simp at eq₁
      rw [vf₂.curr, eq₁.1]
      refine h c' ?_
      rw [←List.mem_reverse, eq₂]
      simp

end String.Iterator

namespace String.Pos.Raw

/--
A variant of `Valid` that allows past-one position that represents the position after running
a search at the end of the string.
-/
def ValidPlus (s : String) (p : Pos.Raw) :=
  p.Valid s ∨ p = s.endPos.offsetBy ⟨1⟩

theorem Valid.validPlus {s : String} {p : Pos.Raw} : p.Valid s → p.ValidPlus s := .inl

theorem next_endPos {s : String} : s.endPos.next s = s.endPos.offsetBy ⟨1⟩ := by
  have next_eq := next_of_valid' s.data []
  simp [Char.utf8Size] at next_eq
  simp [endPos, next_eq, offsetBy, Nat.add_comm]

theorem validPlus_of_next_valid {s : String} {p : Pos.Raw} (h : p.Valid s) : (p.next s).ValidPlus s := by
  have : p ≤ s.endPos := Valid.le_endPos h
  cases Nat.lt_or_eq_of_le this with
  | inl lt => exact .inl (valid_next h lt)
  | inr eq =>
    have : p = s.endPos := Pos.Raw.ext eq
    subst p
    exact .inr next_endPos

theorem ValidPlus.valid_of_le {s : String} {p : Pos.Raw} (le : p ≤ s.endPos) (vp : p.ValidPlus s) : p.Valid s := by
  cases vp with
  | inl v => exact v
  | inr eq =>
    subst eq
    have : s.endPos.byteIdx + 1 ≤ s.endPos.byteIdx := by
      simp_all [endPos, offsetBy]
      grind
    grind

end String.Pos.Raw
