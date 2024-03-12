inductive Regex : Type where
  | empty : Regex
  | epsilon : Regex
  | char : Char → Regex
  | group : Nat → Regex → Regex
  | alternate : Regex → Regex → Regex
  | concat : Regex → Regex → Regex
  | star : Regex → Regex
  | classes : Array (Char × Char) → Regex
deriving Repr, Inhabited

inductive Regex.matches : String → Regex → Prop where
  | char (c : Char) (eq : s = ⟨[c]⟩): Regex.matches s (.char c)
  | epsilon (eq : s = "") : Regex.matches s .epsilon
  | group (m : Regex.matches s r) : Regex.matches s (.group i r)
  | alternateLeft {s : String} {r₁ r₂ : Regex} : Regex.matches s r₁ → Regex.matches s (.alternate r₁ r₂)
  | alternateRight {s : String} {r₁ r₂ : Regex} : Regex.matches s r₂ → Regex.matches s (.alternate r₁ r₂)
  | concat (s s₁ s₂ : String) (r₁ r₂ : Regex) (eq : s = s₁ ++ s₂) :
    Regex.matches s₁ r₁ → Regex.matches s₂ r₂ → Regex.matches s (.concat r₁ r₂)
  | starEpsilon (eq : s = "") : Regex.matches s (.star r)
  | starConcat (s s₁ s₂ : String) (r : Regex) (eq : s = s₁ ++ s₂) :
    Regex.matches s₁ r → Regex.matches s₂ (.star r) → Regex.matches s (.star r)

theorem Regex.empty_not_matches {s : String} (m : Regex.empty.matches s) : False := nomatch m

theorem Regex.epsilon_matches_empty : Regex.matches "" .epsilon := .epsilon rfl

theorem Regex.epsilon_matches_only_empty (s : String) (m : Regex.matches s .epsilon) : s = "" :=
  match s, m with
  | _, .epsilon eq => eq

theorem Regex.char_matches (m : Regex.matches s (.char c)) : s = ⟨[c]⟩ :=
  match s, m with
  | _, .char _ eq => eq

theorem Regex.group_matches : Regex.matches s (.group i r) ↔ Regex.matches s r :=
  ⟨fun | .group m => m, .group⟩

theorem Regex.alternate_matches_or : Regex.matches s (.alternate r₁ r₂) ↔ Regex.matches s r₁ ∨ Regex.matches s r₂ :=
  ⟨fun
    | .alternateLeft m => Or.inl m
    | .alternateRight m => Or.inr m,
   fun
    | Or.inl m => .alternateLeft m
    | Or.inr m => .alternateRight m⟩

theorem Regex.concat_matches : Regex.matches s (.concat r₁ r₂) ↔ ∃s₁ s₂, s = s₁ ++ s₂ ∧ Regex.matches s₁ r₁ ∧ Regex.matches s₂ r₂ :=
  ⟨fun | .concat _ _ _ _ _ eq m₁ m₂ => ⟨_, _, eq, m₁, m₂⟩,
   fun ⟨s₁, s₂, eq, m₁, m₂⟩ => .concat s s₁ s₂ r₁ r₂ eq m₁ m₂⟩
