import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image

-- Port of https://github.com/desi-ivanov/agda-regexp-automata/blob/master/Regexp/Nfa.agda

namespace Regex2

structure NFA (n : Nat) where
  start : Fin n
  δ : Fin n → Char → Finset (Fin n)
  final : Finset (Fin n)

namespace NFA

def accepts (nfa : NFA n) (i : Fin n) : List Char → Bool
  | [] => i ∈ nfa.final
  | c :: cs => ∃ j, j ∈ nfa.δ i c ∧ nfa.accepts j cs

theorem accepts_cons {nfa : NFA n} {i j : Fin n} {c : Char} {cs : List Char}
  (step : j ∈ nfa.δ i c) (rest : nfa.accepts j cs) :
  nfa.accepts i (c :: cs) := by
  simp [accepts]
  exact ⟨j, step, rest⟩

infix:60 "⇓" => fun nfa s => NFA.accepts nfa (NFA.start nfa) s

inductive path (nfa : NFA n) : Fin n → List Char → Prop where
  | nil : ∀ {i}, i ∈ nfa.final → NFA.path nfa i []
  | cons : ∀ {i j c cs}, j ∈ nfa.δ i c → NFA.path nfa j cs → NFA.path nfa i (c :: cs)

theorem path_iff_accepts {nfa : NFA n} : nfa.path i s ↔ nfa.accepts i s := by
  apply Iff.intro
  . intro p
    induction p with
    | nil step => simp [accepts, step]
    | cons step _ ih => simp [accepts]; exact ⟨_, step, ih⟩
  . intro acc
    induction s generalizing i with
    | nil => simp [accepts] at acc; exact path.nil acc
    | cons _ _ ih =>
      simp [accepts] at acc
      let ⟨_, step, rest⟩ := acc
      exact .cons step (ih rest)

-- Union, Concatenation, and Kleene star

def embedL : Fin n ↪ Fin (n + m) :=
  let f : Fin n → Fin (n + m) := fun i => i.castLE (Nat.le_add_right _ _)
  have inj (i j : Fin n) (h : f i = f j) : i = j := by
    simp [Fin.ext_iff] at h
    exact Fin.ext h
  ⟨f, inj⟩
def embedR : Fin m ↪ Fin (n + m) :=
  let f : Fin m → Fin (n + m) := fun i => i.natAdd n
  have inj (i j : Fin m) (h : f i = f j) : i = j := by
    simp [Fin.ext_iff] at h
    exact Fin.ext h
  ⟨f, inj⟩

@[simp]
theorem ne_embedL_embedR (i : Fin n) (j : Fin m) : embedL i ≠ embedR j := by
  apply Fin.ne_of_val_ne
  simp [embedL, embedR]
  apply Nat.ne_of_lt
  exact Nat.lt_of_lt_of_le i.isLt (Nat.le_add_right _ _)

@[simp]
theorem ne_embedR_embedL (i : Fin n) (j : Fin m) : embedR j ≠ embedL i := by
  apply ne_comm.mp (ne_embedL_embedR i j)

def splitAt (i : Fin (n + m)) : Fin n ⊕ Fin m :=
  if h : i.val < n then
    Sum.inl ⟨i.val, h⟩
  else
    let j : Fin m := ⟨i.val - n, Nat.sub_lt_left_of_lt_add (Nat.ge_of_not_lt h) i.isLt⟩
    Sum.inr j

@[simp]
theorem splitAt_embedL (i : Fin n) : splitAt (embedL i : Fin (n + m)) = Sum.inl i := by
  simp [embedL, splitAt]

@[simp]
theorem splitAt_embedR (i : Fin m) : splitAt (embedR i : Fin (n + m)) = Sum.inr i := by
  simp [embedR, splitAt]

@[simp]
theorem mem_embedL_union (i : Fin n) (S₁ : Finset (Fin n)) (S₂ : Finset (Fin m)) :
  embedL i ∈ S₁.map embedL ∪ S₂.map embedR ↔ i ∈ S₁ := by simp

@[simp]
theorem mem_embedR_union (i : Fin m) (S₁ : Finset (Fin n)) (S₂ : Finset (Fin m)) :
  embedR i ∈ S₁.map embedL ∪ S₂.map embedR ↔ i ∈ S₂ := by simp

def union (nfa₁ : NFA n) (nfa₂ : NFA m) : NFA (1 + n + m) :=
  let δ (i : Fin (1 + n + m)) c :=
    match splitAt i with
    | .inl i =>
      match splitAt i with
      | .inl _ => ((nfa₁.δ nfa₁.start c).map embedR).map embedL ∪ (nfa₂.δ nfa₂.start c).map embedR
      | .inr i => ((nfa₁.δ i c).map embedR).map embedL
    | .inr i => (nfa₂.δ i c).map embedR
  let sf : Finset (Fin (1 + n + m)) :=
    if nfa₁ ⇓ [] && nfa₂ ⇓ [] then
      {⟨0, by simp⟩}
    else
      ∅
  { start := ⟨0, by simp⟩,
    δ := δ,
    final := sf ∪ (nfa₁.final.map embedR).map embedL ∪ nfa₂.final.map embedR }

def concat (nfa₁ : NFA n) (nfa₂ : NFA m) : NFA (1 + n + m) :=
  let zero : Fin 1 := ⟨0, by decide⟩
  let δ (i : Fin (1 + n + m)) c :=
    match splitAt i with
    | .inl i =>
      match splitAt i with
      | .inl _ =>
        let start₂ := if nfa₁ ⇓ [] then
          nfa₂.δ nfa₂.start c
        else
          ∅
        ((nfa₁.δ nfa₁.start c).map embedR).map embedL ∪ start₂.map embedR
      | .inr i =>
        let start₂ := if i ∈ nfa₁.final then
          nfa₂.δ nfa₂.start c
        else
          ∅
        ((nfa₁.δ i c).map embedR).map embedL ∪ start₂.map embedR
    | .inr i => (nfa₂.δ i c).map embedR
  let final :=
    match nfa₁ ⇓ [], nfa₂ ⇓ [] with
    | true, true => (Finset.map embedL {zero} ∪ nfa₁.final.map embedR).map embedL ∪ nfa₂.final.map embedR
    | false, true => (nfa₁.final.map embedR).map embedL ∪ nfa₂.final.map embedR
    | _, false => nfa₂.final.map embedR

  { start := embedL (embedL zero),
    δ := δ,
    final := final }

def star (nfa : NFA n) : NFA (1 + n) :=
  let zero := ⟨0, by simp⟩
  let δ (i : Fin (1 + n)) c :=
    match splitAt i with
    | .inl _ => (nfa.δ nfa.start c).map embedR
    | .inr i => (nfa.δ i c).map embedR
  { start := zero,
    δ := δ,
    final := {⟨0, by simp⟩} ∪ nfa.final.map embedR }

-- Correctness proofs

theorem concat_preserve₂ {nfa₂ : NFA m} {i : Fin m} {cs : List Char} :
  (concat nfa₁ nfa₂).accepts (embedR i) cs ↔ nfa₂.accepts i cs := by
  apply Iff.intro
  . intro acc
    induction cs generalizing i with
    | nil =>
      simp [accepts, concat] at *
      split at acc <;> simp at acc <;> exact acc
    | cons head tail ih =>
      simp [accepts] at *
      let ⟨j, step, rest⟩ := acc
      simp [concat] at step
      let ⟨j', step', eq⟩ := step
      exact ⟨j', step', ih (eq.symm ▸ rest)⟩
  . intro acc
    induction cs generalizing i with
    | nil =>
      simp [accepts, concat] at *
      split <;> simp [acc]
    | cons head tail ih =>
      simp [accepts] at *
      let ⟨j, step, rest⟩ := acc
      exact ⟨embedR j, by simp [concat, step], ih rest⟩

theorem concat_preserve₁ {nfa₁ : NFA n} {i : Fin n} {cs : List Char} :
  (concat nfa₁ nfa₂).accepts (embedL (embedR i)) cs ↔
  ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ nfa₁.accepts i cs₁ ∧ nfa₂ ⇓ cs₂ := by
  apply Iff.intro
  . intro acc
    induction cs generalizing i with
    | nil =>
      simp [accepts, concat] at *
      split at acc <;> simp at acc
      next _ h₂ =>
        exists [], []
        simp
        exact ⟨by simp [accepts, acc], h₂⟩
      next _ h₂ =>
        exists [], []
        simp
        exact ⟨by simp [accepts, acc], h₂⟩
    | cons head tail ih =>
      simp [accepts] at acc
      let ⟨j', step', rest'⟩ := acc
      simp [concat] at step'
      match step' with
      | .inl ⟨j, step, eq⟩ =>
        let ⟨cs₁, cs₂, eqs, acc₁, acc₂⟩ := ih (eq.symm ▸ rest')
        exact ⟨head :: cs₁, cs₂, by simp [eqs], by simp [accepts]; exact ⟨j, step, acc₁⟩, acc₂⟩
      | .inr ⟨j, step, eq⟩ =>
        split at step <;> try simp at step
        next h =>
          have : embedR j ∈ (concat nfa₁ nfa₂).δ (embedR nfa₂.start) head := by
            simp [concat]
            exact step
          have : (concat nfa₁ nfa₂).accepts (embedR nfa₂.start) (head :: tail) :=
            accepts_cons this (eq.symm ▸ rest')
          exact ⟨[], head :: tail, by simp, by simp [accepts, h], concat_preserve₂.mp this⟩
  . intro accs
    let ⟨cs₁, cs₂, eqs, acc₁, acc₂⟩ := accs
    induction cs₁ generalizing i cs with
    | nil =>
      have final : i ∈ nfa₁.final := by
        simp [accepts] at acc₁
        exact acc₁
      simp [eqs]
      cases cs₂ with
      | nil =>
        have : nfa₂.start ∈ nfa₂.final := by
          simp [accepts] at acc₂
          exact acc₂
        simp [accepts, concat, this]
        split <;> simp [final] ; contradiction
      | cons c cs₂ =>
        simp [accepts] at *
        let ⟨j, step, rest⟩ := acc₂
        have step : embedR j ∈ (concat nfa₁ nfa₂).δ (embedL (embedR i)) c := by
          simp [concat, acc₁, step]
        have rest : (concat nfa₁ nfa₂).accepts (embedR j) cs₂ := concat_preserve₂.mpr rest
        exact ⟨embedR j, step, rest⟩
    | cons head tail ih =>
      simp [eqs, accepts]
      simp [accepts] at acc₁
      let ⟨j, step, rest⟩ := acc₁
      have ih := ih ⟨tail, cs₂, rfl, rest, acc₂⟩ rfl rest
      exact ⟨embedL (embedR j), by simp [concat, step], ih⟩

theorem concat_correct :
  (concat nfa₁ nfa₂) ⇓ cs ↔ ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ nfa₁ ⇓ cs₁ ∧ nfa₂ ⇓ cs₂ := by
  apply Iff.intro
  . intro acc
    cases cs with
    | nil =>
      simp [accepts, concat] at acc
      split at acc <;> simp at acc
      exists [], []
    | cons head tail =>
      simp [accepts] at acc
      let ⟨j, step, rest⟩ := acc
      simp [concat, accepts] at step
      cases step with
      | inl h =>
        let ⟨j', step', eq⟩ := h
        let ⟨cs₁, cs₂, eqs, acc₁, acc₂⟩ := concat_preserve₁.mp (eq.symm ▸ rest)
        exact ⟨head :: cs₁, cs₂, by simp [eqs], accepts_cons step' acc₁, acc₂⟩
      | inr h =>
        let ⟨j', step', eq⟩ := h
        split at step' <;> try simp at step'
        next h =>
          refine ⟨[], head :: tail, rfl, by simp [accepts, h], ?_⟩
          simp [accepts]
          refine ⟨j', step', ?_⟩
          exact concat_preserve₂.mp (eq.symm ▸ rest)
  . intro accs
    cases cs with
    | nil =>
      let ⟨cs₁, cs₂, eqs, acc₁, acc₂⟩ := accs
      have eqs := List.append_eq_nil.mp eqs.symm
      simp [accepts, eqs] at acc₁ acc₂
      simp [accepts, concat, acc₁, acc₂]
    | cons head tail =>
      let acc := concat_preserve₁.mpr accs
      simp [accepts] at acc
      simp [accepts]
      let ⟨j, step, rest⟩ := acc
      refine ⟨j, ?_, rest⟩
      apply Finset.mem_of_subset _ step
      simp [concat, accepts]

end NFA

end Regex2
