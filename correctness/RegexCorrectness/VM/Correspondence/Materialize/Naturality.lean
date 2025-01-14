import RegexCorrectness.Data.Expr.Semantics
import RegexCorrectness.NFA.Semantics.Equivalence
import RegexCorrectness.VM.Correspondence.Materialize.Lemmas

set_option autoImplicit false

open Regex.Data (Expr)
open String (Pos)

namespace Regex.NFA

/--
Under suitable conditions, the equivalence between capture groups and NFA buffer updates can be
naturally transformed into a materialized version.
-/
theorem EquivUpdate.materialize {e : Expr} {n span span' groups updates}
  (c : e.Captures span span' groups) (disj : e.Disjoint)
  (eqv : EquivUpdate groups updates) :
  EquivMaterializedUpdate (materializeRegexGroups groups) (materializeUpdates n updates) := by
  induction c generalizing updates with
  | char | sparse | epsilon | starEpsilon =>
    cases eqv with
    | empty => simp [EquivMaterializedUpdate]
  | @group span span' groups tag e c ih =>
    simp [Expr.Disjoint] at disj
    cases eqv with
    | @group groups updates _ _ _ eqv =>
      have ih := ih disj.2 eqv
      simp [materializeUpdates]
      rw [materializeUpdatesAux_cons_of_not_in ?_]
      . simp [materializeUpdatesAux_snoc]
        intro tag'
        simp
        apply And.intro
        . intro h₁
          if h : tag = tag' then
            simp [h]
          else
            have h' : 2 * tag ≠ 2 * tag' := by omega
            have h'' : 2 * tag + 1 ≠ 2 * tag' := by omega
            simp [h, h', h'']
            exact (ih tag').1 h₁
        . intro h₂
          if h : tag = tag' then
            simp [h]
          else
            have h' : 2 * tag ≠ 2 * tag' + 1 := by omega
            have h'' : 2 * tag + 1 ≠ 2 * tag' + 1 := by omega
            simp [h, h', h'']
            exact (ih tag').2 h₂
      . intro offset pos mem
        simp at mem
        cases mem with
        | inl mem =>
          have ⟨tag', first, last, mem', eq⟩ := eqv.mem_groups_of_mem_updates mem
          cases eq with
          | inl eq =>
            suffices tag ≠ tag' by omega
            intro eq
            subst tag'
            have mem_tags := c.mem_tags_of_mem_groups tag first last mem'
            exact disj.1 mem_tags
          | inr eq => omega
        | inr eq => omega
  | alternateLeft _ ih =>
    simp [Expr.Disjoint] at disj
    exact ih disj.2.1 eqv
  | alternateRight _ ih =>
    simp [Expr.Disjoint] at disj
    exact ih disj.2.2 eqv
  | concat _ _ ih₁ ih₂ =>
    simp [Expr.Disjoint] at disj
    cases eqv with
    | @concat _ _ update₁ update₂ eqv₁ eqv₂ =>
      have ih₁ := ih₁ disj.2.1 eqv₁
      have ih₂ := ih₂ disj.2.2 eqv₂
      exact concat ih₁ ih₂
  | starConcat _ _ ih₁ ih₂ =>
    simp [Expr.Disjoint] at disj
    cases eqv with
    | @concat _ _ update₁ update₂ eqv₁ eqv₂ =>
      have ih₁ := ih₁ disj eqv₁
      have ih₂ := ih₂ (by simp [Expr.Disjoint, disj]) eqv₂
      exact concat ih₁ ih₂
where
  concat {g₁ g₂ u₁ u₂}
    (eqv₁ : EquivMaterializedUpdate (materializeRegexGroups g₁) (materializeUpdates n u₁))
    (eqv₂ : EquivMaterializedUpdate (materializeRegexGroups g₂) (materializeUpdates n u₂)) :
    EquivMaterializedUpdate (materializeRegexGroups (.concat g₁ g₂)) (materializeUpdates n (u₁ ++ u₂)) := by
    intro tag
    apply And.intro
    . intro h₁
      simp [materializeUpdates_append_getElem]
      match h : materializeRegexGroups g₂ tag with
      | .some (first, last) =>
        have := (eqv₂ tag).1 h₁
        simp [h] at this
        simp [←this]
      | .none =>
        have := (eqv₂ tag).1 h₁
        simp [h] at this
        simp [←this, (eqv₁ tag).1 h₁]
    . intro h₂
      simp [materializeUpdates_append_getElem]
      match h : materializeRegexGroups g₂ tag with
      | .some (first, last) =>
        have := (eqv₂ tag).2 h₂
        simp [h] at this
        simp [←this]
      | .none =>
        have := (eqv₂ tag).2 h₂
        simp [h] at this
        simp [←this, (eqv₁ tag).2 h₂]


end Regex.NFA
