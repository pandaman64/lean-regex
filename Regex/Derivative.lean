import Regex.Regex

def Regex.matches_empty (self : Regex) : Bool :=
  match self with
  | .empty | .char _ => false
  | .epsilon | .star _ => true
  | .alternate r₁ r₂ => r₁.matches_empty || r₂.matches_empty
  | .concat r₁ r₂ => r₁.matches_empty && r₂.matches_empty

theorem List.empty_of_length_eq_zero {α : Type} {x : List α} : x.length = 0 → x = [] := by
  match x with
  | [] => simp
  | cons _ _ => intros; contradiction

theorem List.append_empty {α : Type} {x y : List α} : x ++ y = [] → x = [] ∧ y = [] := by
  intro h
  have h : (x ++ y).length = 0 := by
    rw [h]
    simp
  rw [List.length_append] at h
  have hx : length x ≤ 0 := by
    rw [←h]
    apply Nat.le_add_right
  have hy : y.length ≤ 0 := by
    rw [←h]
    apply Nat.le_add_left
  exact ⟨
    List.empty_of_length_eq_zero (Nat.eq_zero_of_le_zero hx),
    List.empty_of_length_eq_zero (Nat.eq_zero_of_le_zero hy)
  ⟩

theorem String.mk_data {s : String} : s.data = d → s = ⟨d⟩ := by
  induction s with
  | mk d' => simp; intro h; rw [h]

theorem String.data_of_append_eq_append_of_data {s₁ s₂ : String} :
  (s₁ ++ s₂).data = s₁.data ++ s₂.data := by
  match s₁, s₂ with
  | mk d₁, mk d₂ =>
    simp
    rfl

theorem String.empty_of_append {s₁ s₂ : String} : s₁ ++ s₂ = "" → s₁ = "" ∧ s₂ = "" := by
  intro h
  have h : (s₁ ++ s₂).data = [] := by rw [h]
  have ⟨h₁, h₂⟩ := List.append_empty h
  exact ⟨String.mk_data h₁, String.mk_data h₂⟩

theorem Regex.matches_empty_eq_matches_empty (r : Regex) :
  r.matches "" ↔ r.matches_empty := by
  induction r <;> simp [matches_empty]
  case empty => apply empty_not_matches
  case epsilon => exact epsilon_matches_empty
  case char c =>
    intro m
    apply String.noConfusion (Regex.char_matches m)
    simp
  case alternate iff₁ iff₂ =>
    rw [alternate_matches_or, iff₁, iff₂]
    simp
  case concat r₁ r₂ iff₁ iff₂ =>
    rw [concat_matches]
    apply Iff.intro
    . intro h
      let ⟨s₁, s₂, h, m₁, m₂⟩ := h
      let ⟨h₁, h₂⟩ := String.empty_of_append h.symm
      subst h₁ h₂
      exact ⟨iff₁.mp m₁, iff₂.mp m₂⟩
    . intro h
      exists "", ""
      apply And.intro
      . decide
      . simp [*]
  case star r _ => exact .starEpsilon rfl

def Regex.derivative (c : Char) : Regex → Regex
  | .empty => .empty
  | .epsilon => .empty
  | .char c' => if c = c' then .epsilon else .empty
  | .alternate r₁ r₂ => .alternate (derivative c r₁) (derivative c r₂)
  | .concat r₁ r₂ =>
    if r₁.matches_empty then .alternate (.concat (derivative c r₁) r₂) (derivative c r₂)
    else .concat (derivative c r₁) r₂
  | .star r => .concat (derivative c r) (.star r)

def Regex.matches_derivative (cs : List Char) (r : Regex) : Bool :=
  match cs with
  | [] => r.matches_empty
  | c :: cs => r.derivative c |>.matches_derivative cs

theorem List.cons_eq_append_split (h : c :: cs = s₁ ++ s₂) :
  (s₁ = [] ∧ c :: cs = s₂) ∨ (∃s₁', s₁ = c :: s₁' ∧ cs = s₁' ++ s₂) := by
  cases s₁ with
  | nil => apply Or.inl; simp [h]
  | cons c' s₁ =>
    apply Or.inr
    exists s₁
    apply List.noConfusion h
    intro heq teq
    simp [heq, teq]

theorem String.cons_eq_append_split {c : Char} {cs : List Char} {s₁ s₂ : String}
  (h : ⟨c :: cs⟩ = s₁ ++ s₂) :
  (s₁ = "" ∧ ⟨c :: cs⟩ = s₂) ∨ (∃s₁' : String, s₁ = ⟨c :: s₁'.data⟩ ∧ ⟨cs⟩ = s₁' ++ s₂) := by
  have h' : c :: cs = s₁.data ++ s₂.data := by
    apply String.noConfusion h
    intro eq
    exact eq
  match List.cons_eq_append_split h' with
  | .inl h => exact .inl ⟨mk_data h.left, mk_data h.right⟩
  | .inr h =>
    let ⟨s₁', h₁, h₂⟩ := h
    apply Or.inr
    exact ⟨⟨s₁'⟩, mk_data h₁, mk_data h₂⟩

theorem String.empty_append_left (s : String) : "" ++ s = s := by
  have : ("" ++ s).data = s.data := data_of_append_eq_append_of_data
  exact String.mk_data this

theorem Regex.matches_of_alternate_matches (h : Regex.matches s (.alternate r r)) :
  Regex.matches s r := by
  match h with
  | .alternateLeft m => exact m
  | .alternateRight m => exact m

theorem Regex.derivative_matches_of_matches {c : Char} {cs : List Char} {r : Regex}
  (m : r.matches ⟨c :: cs⟩) : (r.derivative c).matches ⟨cs⟩ := by
  generalize h : String.mk (c :: cs) = s
  rw [h] at m
  induction m generalizing cs with
  | char c' eq =>
    subst eq
    apply String.noConfusion h
    intro eq
    apply List.noConfusion eq
    intro ceq cseq
    rw [ceq, cseq]
    simp [derivative]
    exact .epsilon rfl
  | epsilon eq => subst eq; apply String.noConfusion h; intros; contradiction
  | alternateLeft _ ih => exact .alternateLeft (ih h)
  | alternateRight _ ih => exact .alternateRight (ih h)
  | concat s s₁ s₂ r₁ r₂ eq m₁ m₂ ih₁ ih₂ =>
    simp [derivative]
    rw [eq] at h
    cases String.cons_eq_append_split h with
    | inl h =>
      let ⟨h₁, h₂⟩ := h
      subst h₁ h₂
      have : matches_empty r₁ := (matches_empty_eq_matches_empty r₁).mp m₁
      simp [this]
      exact .alternateRight (ih₂ rfl)
    | inr h =>
      let ⟨s₁', h₁, h₂⟩ := h
      have m : Regex.matches ⟨cs⟩ (.concat (derivative c r₁) r₂) := by
        rw [h₂]
        exact .concat _ _ _ _ _ rfl (ih₁ h₁.symm) m₂
      cases r₁.matches_empty with
      | true => simp; exact .alternateLeft m
      | false => simp; exact m
  | @starEpsilon s r eq =>
    simp [derivative]
    subst eq
    apply String.noConfusion h
    intro h
    contradiction
  | @starConcat s s₁ s₂ r eq _ m₂ ih₁ ih₂ =>
    cases String.cons_eq_append_split (eq ▸ h) with
    | inl h => exact ih₂ h.right
    | inr h =>
      simp [derivative]
      let ⟨s₁', h₁, h₂⟩ := h
      have ih₁ := ih₁ h₁.symm
      exact .concat ⟨cs⟩ s₁' s₂ _ _ h₂ ih₁ m₂

theorem Regex.matches_of_derivative_matches {c : Char} {cs : List Char} {r : Regex}
  (m : (r.derivative c).matches ⟨cs⟩) : r.matches ⟨c :: cs⟩ := by
  -- How to use this?
  let rec concat_lemma {r₁ r₂ : Regex} (m : Regex.matches ⟨cs⟩ (.concat (derivative c r₁) r₂)) :
    Regex.matches ⟨c :: cs⟩ (.concat r₁ r₂) := by
    let ⟨s₁, s₂, eq, m₁, m₂⟩ := concat_matches.mp m
    let m₁' := matches_of_derivative_matches m₁
    have eq' : ⟨c :: cs⟩ = ⟨c :: s₁.data⟩ ++ s₂ := by
      show (⟨c :: cs⟩ : String) = ⟨c :: s₁.data ++ s₂.data⟩
      have : c :: cs = c :: s₁.data ++ s₂.data := by
        apply String.noConfusion eq
        intro eq
        simp [eq]
      rw [this]
    exact .concat _ _ _ _ _ eq' m₁' m₂

  match r with
  | .empty | .epsilon => simp [derivative] at m; contradiction
  | .char c' =>
    simp [derivative] at m
    match decEq c c' with
    | isTrue eq =>
      subst eq
      simp at m
      have : ⟨cs⟩ = "" := epsilon_matches_only_empty ⟨cs⟩ m
      apply String.noConfusion this
      intro eq
      subst eq
      exact .char c rfl
    | isFalse ne =>
      simp [ne] at m
      contradiction
  | .alternate r₁ r₂ =>
    simp [derivative] at m
    match m with
    | .alternateLeft m => exact .alternateLeft (matches_of_derivative_matches m)
    | .alternateRight m => exact .alternateRight (matches_of_derivative_matches m)
  | .concat r₁ r₂ =>
    simp [derivative] at m
    match e : r₁.matches_empty, m with
    | true, m =>
      simp at m
      match m with
      | .alternateLeft m =>
        -- TODO: コピペ
        let ⟨s₁, s₂, eq, m₁, m₂⟩ := concat_matches.mp m
        let m₁' := matches_of_derivative_matches m₁
        have eq' : ⟨c :: cs⟩ = ⟨c :: s₁.data⟩ ++ s₂ := by
          show (⟨c :: cs⟩ : String) = ⟨c :: s₁.data ++ s₂.data⟩
          have : c :: cs = c :: s₁.data ++ s₂.data := by
            apply String.noConfusion eq
            intro eq
            simp [eq]
          rw [this]
        exact .concat _ _ _ _ _ eq' m₁' m₂
      | .alternateRight m =>
        let m₁ := (matches_empty_eq_matches_empty _).mpr e
        let m₂ := matches_of_derivative_matches m
        exact .concat _ _ _ _ _ (Eq.symm (String.empty_append_left _)) m₁ m₂
    | false, m =>
      simp at m
      let ⟨s₁, s₂, eq, m₁, m₂⟩ := concat_matches.mp m
      let m₁' := matches_of_derivative_matches m₁
      have eq' : ⟨c :: cs⟩ = ⟨c :: s₁.data⟩ ++ s₂ := by
        show (⟨c :: cs⟩ : String) = ⟨c :: s₁.data ++ s₂.data⟩
        have : c :: cs = c :: s₁.data ++ s₂.data := by
          apply String.noConfusion eq
          intro eq
          simp [eq]
        rw [this]
      exact .concat _ _ _ _ _ eq' m₁' m₂
  | .star r =>
    simp [derivative] at m
    let ⟨s₁, s₂, eq, m₁, m₂⟩ := concat_matches.mp m
    let m₁' := matches_of_derivative_matches m₁
    have eq' : ⟨c :: cs⟩ = ⟨c :: s₁.data⟩ ++ s₂ := by
      show (⟨c :: cs⟩ : String) = ⟨c :: s₁.data ++ s₂.data⟩
      have : c :: cs = c :: s₁.data ++ s₂.data := by
        apply String.noConfusion eq
        intro eq
        simp [eq]
      rw [this]
    exact .starConcat _ _ _ _ eq' m₁' m₂

theorem Regex.derivative_matches (c : Char) (cs : List Char) (r : Regex) :
  r.matches ⟨c :: cs⟩ ↔ (r.derivative c).matches ⟨cs⟩ :=
  ⟨Regex.derivative_matches_of_matches, Regex.matches_of_derivative_matches⟩

theorem Regex.matches_iff_matches_derivative {cs : List Char} {r : Regex} :
  r.matches ⟨cs⟩ ↔ r.matches_derivative cs := by
  apply Iff.intro
  . intro m
    induction cs generalizing r with
    | nil =>
      simp [matches_derivative]
      exact (matches_empty_eq_matches_empty r).mp m
    | cons c cs ih =>
      simp [matches_derivative]
      have m := (derivative_matches c cs r).mp m
      exact ih m
  . intro md
    induction cs generalizing r with
    | nil =>
      simp [matches_derivative] at md
      exact (matches_empty_eq_matches_empty r).mpr md
    | cons c cs ih =>
      simp [matches_derivative] at md
      exact (derivative_matches c cs r).mpr (ih md)
