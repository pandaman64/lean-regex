import Regex.Classes

inductive Regex : Type where
  | empty : Regex
  | epsilon : Regex
  | char : Char → Regex
  | group : Nat → Regex → Regex
  | alternate : Regex → Regex → Regex
  | concat : Regex → Regex → Regex
  | star : Regex → Regex
  | classes : Regex.Classes → Regex
deriving Repr, Inhabited

inductive Regex.matches : List Char → Regex → Prop where
  | char (c : Char) : Regex.matches [c] (.char c)
  | sparse (cs : Classes) (c : Char) (h : c ∈ cs) : Regex.matches [c] (.classes cs)
  | epsilon : Regex.matches [] .epsilon
  | group (m : Regex.matches s r) : Regex.matches s (.group i r)
  | alternateLeft {cs : List Char} {r₁ r₂ : Regex} : Regex.matches cs r₁ → Regex.matches cs (.alternate r₁ r₂)
  | alternateRight {cs : List Char} {r₁ r₂ : Regex} : Regex.matches cs r₂ → Regex.matches cs (.alternate r₁ r₂)
  | concat (cs₁ cs₂ : List Char) (r₁ r₂ : Regex) :
    Regex.matches cs₁ r₁ → Regex.matches cs₂ r₂ → Regex.matches (cs₁ ++ cs₂) (.concat r₁ r₂)
  | starEpsilon : Regex.matches [] (.star r)
  | starConcat (cs₁ cs₂ : List Char) (r : Regex) :
    Regex.matches cs₁ r → Regex.matches cs₂ (.star r) → Regex.matches (cs₁ ++ cs₂) (.star r)

theorem Regex.empty_not_matches (m : Regex.empty.matches cs) : False := nomatch m

theorem Regex.epsilon_matches_empty : Regex.matches [] .epsilon := .epsilon

theorem Regex.epsilon_matches_only_empty (cs : List Char) (m : Regex.matches cs .epsilon) : cs = [] :=
  match m with
  | .epsilon => rfl

theorem Regex.char_matches (m : Regex.matches cs (.char c)) : cs = [c] :=
  match m with
  | .char _ => rfl

theorem Regex.group_matches : Regex.matches cs (.group i r) ↔ Regex.matches cs r :=
  ⟨fun | .group m => m, .group⟩

theorem Regex.alternate_matches_or : Regex.matches cs (.alternate r₁ r₂) ↔ Regex.matches cs r₁ ∨ Regex.matches cs r₂ :=
  ⟨fun
    | .alternateLeft m => Or.inl m
    | .alternateRight m => Or.inr m,
   fun
    | Or.inl m => .alternateLeft m
    | Or.inr m => .alternateRight m⟩

theorem Regex.concat_matches : Regex.matches cs (.concat r₁ r₂) ↔ ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ Regex.matches cs₁ r₁ ∧ Regex.matches cs₂ r₂ :=
  ⟨fun | .concat _ _ _ _ m₁ m₂ => ⟨_, _, rfl, m₁, m₂⟩,
   fun ⟨cs₁, cs₂, eq, m₁, m₂⟩ => eq ▸ .concat cs₁ cs₂ r₁ r₂ m₁ m₂⟩
