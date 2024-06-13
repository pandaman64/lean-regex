import Regex.Data.Expr

namespace Regex.Data

inductive Expr.matches : List Char → Expr → Prop where
  | char (c : Char) : Expr.matches [c] (.char c)
  | sparse (cs : Classes) (c : Char) (h : c ∈ cs) : Expr.matches [c] (.classes cs)
  | epsilon : Expr.matches [] .epsilon
  | group (m : Expr.matches s r) : Expr.matches s (.group i r)
  | alternateLeft {cs : List Char} {r₁ r₂ : Expr} : Expr.matches cs r₁ → Expr.matches cs (.alternate r₁ r₂)
  | alternateRight {cs : List Char} {r₁ r₂ : Expr} : Expr.matches cs r₂ → Expr.matches cs (.alternate r₁ r₂)
  | concat (cs₁ cs₂ : List Char) (r₁ r₂ : Expr) :
    Expr.matches cs₁ r₁ → Expr.matches cs₂ r₂ → Expr.matches (cs₁ ++ cs₂) (.concat r₁ r₂)
  | starEpsilon : Expr.matches [] (.star r)
  | starConcat (cs₁ cs₂ : List Char) (r : Expr) :
    Expr.matches cs₁ r → Expr.matches cs₂ (.star r) → Expr.matches (cs₁ ++ cs₂) (.star r)

-- theorem Expr.empty_not_matches (m : Expr.empty.matches cs) : False := nomatch m

-- theorem Expr.epsilon_matches_empty : Expr.matches [] .epsilon := .epsilon

-- theorem Expr.epsilon_matches_only_empty (cs : List Char) (m : Expr.matches cs .epsilon) : cs = [] :=
--   match m with
--   | .epsilon => rfl

-- theorem Expr.char_matches (m : Expr.matches cs (.char c)) : cs = [c] :=
--   match m with
--   | .char _ => rfl

-- theorem Expr.group_matches : Expr.matches cs (.group i r) ↔ Expr.matches cs r :=
--   ⟨fun | .group m => m, .group⟩

-- theorem Expr.alternate_matches_or : Expr.matches cs (.alternate r₁ r₂) ↔ Expr.matches cs r₁ ∨ Expr.matches cs r₂ :=
--   ⟨fun
--     | .alternateLeft m => Or.inl m
--     | .alternateRight m => Or.inr m,
--    fun
--     | Or.inl m => .alternateLeft m
--     | Or.inr m => .alternateRight m⟩

-- theorem Expr.concat_matches : Expr.matches cs (.concat r₁ r₂) ↔ ∃ cs₁ cs₂, cs = cs₁ ++ cs₂ ∧ Expr.matches cs₁ r₁ ∧ Expr.matches cs₂ r₂ :=
--   ⟨fun | .concat _ _ _ _ m₁ m₂ => ⟨_, _, rfl, m₁, m₂⟩,
--    fun ⟨cs₁, cs₂, eq, m₁, m₂⟩ => eq ▸ .concat cs₁ cs₂ r₁ r₂ m₁ m₂⟩

end Regex.Data
