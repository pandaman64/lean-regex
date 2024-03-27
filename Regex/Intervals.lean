def Char.MAX_UNICODE : Nat := 0x10FFFF

theorem Char.isAlawysLessOrEqToMax (c : Char) : c.val.val ≤ MAX_UNICODE := by
  let s := c.valid
  simp [UInt32.isValidChar, Nat.isValidChar, UInt32.isValidChar, UInt32.toNat] at s
  cases s with
  | inl s => exact Nat.le_trans (Nat.le_of_lt s) (by decide)
  | inr s => exact Nat.le_trans (Nat.le_of_lt_succ s.right) (by decide)

theorem Nat.toNonNeg {m n : Nat} (h : m ≥ n) : Int.NonNeg (Int.ofNat m - Int.ofNat n) := by
  simp [HSub.hSub]
  simp [Sub.sub, Int.sub, Neg.neg, Int.neg, Int.negOfNat, Int.negSucc, HAdd.hAdd]
  simp [Add.add, Int.add, Int.subNatNat];
  match m, n with
  | zero, succ n   => contradiction
  | succ m, succ n =>
    simp [HSub.hSub]
    simp [Sub.sub]
    let p := Nat.sub_eq_zero_of_le h
    rw [p]
    simp
    exact Int.NonNeg.mk (succ m - succ n)
  | a,    zero  =>
    simp [Add.add, Int.add]
    exact Int.NonNeg.mk a

def Nat.inverseOfLess {m n : Nat} (h : ¬ (m ≤ n)) : (succ n) ≤ m := by
  match Nat.lt_or_ge n m with
  | Or.inl h1 => exact h1
  | Or.inr h1 => exact False.elim (h h1)

def Intervals : Type := Array {i : (Char × Char) // i.fst.toNat ≤ i.snd.toNat  }

def Intervals.in (int: Intervals) (c: Char) : Bool :=
  int.data.any (λ i => i.val.fst.toNat ≤ c.toNat && c.toNat ≤ i.val.snd.toNat)

def Intervals.InType (int: Intervals) (c: Char) : Prop :=
  ∃ x, x ∈ int.data ∧ (x.val.fst.toNat ≤ c.toNat ∧ c.toNat ≤ x.val.snd.toNat)

def List.if_is (h: x ∈ y) : x ∈ (z :: y) := List.Mem.tail z h

def List.is_in (h: x ∈ y :: ys) (h₂ : x ≠ y) : x ∈ ys :=
  match h with
  | List.Mem.head _   => nomatch h₂ rfl
  | List.Mem.tail _ h => h

def Intervals.in_if_inType (int: Intervals) : ∀ c, int.in c → int.InType c := by
  intro c
  simp [Intervals.in, Intervals.InType]
  match int with
  | ⟨[]⟩      => simp [List.any]
  | ⟨x :: xs⟩ =>
    simp [List.any]
    intro h
    cases h with
    | inl h => exists x; exact ⟨List.Mem.head xs, h⟩
    | inr h =>
      let res := Intervals.in_if_inType ⟨xs⟩ c h
      simp [InType] at res
      exact Exists.elim res (λ x h => ⟨x, ⟨List.if_is h.left, h.right⟩⟩)
termination_by int.data.length

def Intervals.inType_if_in (int: Intervals) : ∀ c, int.InType c → int.in c := by
  intro c
  simp [Intervals.in, Intervals.InType]
  match int with
  | ⟨[]⟩      =>
    simp [List.any]
    exact fun h => nomatch h
  | ⟨x :: xs⟩ =>
    simp [List.any]
    intro h
    apply Exists.elim h
    intro x₂ y
    apply dite (x = x₂)
    · intro h₂
      simp [h₂]
      exact Or.inl y.right
    · intro h₂
      apply Or.inr
      apply Intervals.inType_if_in ⟨xs⟩ c
      simp [InType]
      let h₃ := List.is_in y.left (Ne.intro h₂ |> Ne.symm)
      exact ⟨x₂, ⟨h₃, y.right⟩⟩
termination_by int.data.length

def Intervals.in_iff (int: Intervals) (c: Char) : int.in c ↔ int.InType c :=
  ⟨Intervals.in_if_inType int c, Intervals.inType_if_in int c⟩

instance Membership.Mem : Membership Char Intervals := ⟨flip Intervals.InType⟩

theorem Intervals.emptyDoesNotBelong (c: Char) : c ∉ #[] := fun hp => nomatch hp

theorem Intervals.notEmptyFinGreaterThan0 (int: Intervals) (h: ¬int.isEmpty) : int.size > 0 := by
  simp [Array.isEmpty] at h
  cases Nat.eq_zero_or_pos int.size with
  | inl x => exact absurd x h
  | inr x => exact x

theorem List.has_if_gets (x: List α) (n : Fin x.length) : List.Mem (List.get x n) x :=
  match x with
  | []      => nomatch n
  | x :: xs =>
    match n with
    | ⟨0, _⟩          => by simp [List.get]; exact List.Mem.head xs
    | ⟨Nat.succ n, s⟩ => by
      simp [List.get];
      simp [List.length, HAdd.hAdd, Add.add, Nat.add] at s
      let s := Nat.le_of_lt_succ s
      let n := List.has_if_gets xs ⟨n, s⟩
      exact List.Mem.tail x n

theorem Array.has_if_gets (x : Array α) (n : Fin x.size) : x.get n ∈ x := ⟨List.has_if_gets x.data n⟩

theorem Intervals.not_empty_has_char (int: Intervals) (h: ¬int.isEmpty) : { x : Char // x ∈ int } :=
  if h₁ : int.isEmpty
    then absurd h₁ h
    else
      let s := Intervals.notEmptyFinGreaterThan0 int h
      let x := int.get ⟨0, s⟩
      ⟨x.val.fst, by simp [Membership.mem, flip, Intervals.InType, List.any]
                     exists int.get ⟨0, s⟩
                     exact ⟨List.has_if_gets int.data ⟨0, s⟩, ⟨by simp, (int.get ⟨0, s⟩).property⟩⟩⟩

instance : Repr Intervals where
  reprPrec int _ := repr (int.map (·.val))

def Intervals.empty : Intervals := #[]

def Intervals.append (c : Intervals) (i : Char × Char) (pf: i.fst ≤ i.snd) : Intervals := c.push ⟨i, pf⟩

def Intervals.merge (int: Intervals) : Intervals := Id.run do
  let intervals := int.qsort (λ a b => a.val.1 < b.val.1)
  let mut merged := #[]
  let d := ⟨('0', '0'), by decide⟩

  for interval in intervals do
    if merged.isEmpty || interval.val.fst > (merged.back?.getD d).val.snd then
      merged := merged.push interval
    else
      let m := (merged.getD (merged.size-1) d)
      let s := interval

      let snd : { x : Char // m.val.fst.toNat ≤ x.toNat } :=
        if h : m.val.snd.toNat ≤ s.val.snd.toNat
          then ⟨s.val.snd, Nat.le_trans m.property h⟩
          else ⟨m.val.snd, m.property⟩

      merged  := merged.set! (merged.size - 1) ⟨(m.val.fst, snd.val), snd.property⟩

  return merged

def Intervals.invert (int: Intervals) : Intervals := Id.run do
  let int := int.merge

  let intervals := int.qsort (λ a b => a.val.1 < b.val.1)

  let mut result : Array {i : (Char × Char) // i.fst ≤ i.snd } := #[]
  let mut lastEnd : {i : Int // i ≤ Char.MAX_UNICODE} := ⟨(-1), by decide⟩

  for interval in intervals do
    let start := interval.val.fst.toNat
    let end_ := interval.val.snd.toNat
    let p := Char.isAlawysLessOrEqToMax interval.val.snd

    let m := Char.ofNat (lastEnd.val + 1).toNat
    let n := Char.ofNat (start - 1)

    if h : m <= n then
      result := result.push ⟨(m, n), h⟩

    lastEnd := if end_ > lastEnd.val then ⟨interval.val.snd.toNat, by simp [Char.toNat, UInt32.toNat]; exact (Nat.toNonNeg p)⟩ else lastEnd

    if h : Char.ofNat (lastEnd.val + 1).toNat <= Char.ofNat Char.MAX_UNICODE then
      result := result.push ⟨(Char.ofNat (lastEnd.val + 1).toNat, Char.ofNat Char.MAX_UNICODE), h⟩

  return result
