module

public import RegexCorrectness.Data.Expr.Semantics.Backtracking.Basic
import all RegexCorrectness.Data.Expr.Semantics.Backtracking.Basic

set_option autoImplicit false

open String (Pos)

namespace Regex.Data.Expr.BacktrackingTree

def ActionsDisjoint : List Action → Prop
  | [] => True
  | .expr e :: as => e.Disjoint ∧ ActionsDisjoint as
  | .closeGroup _ :: as => ActionsDisjoint as

@[simp] theorem actionsDisjoint_expr {e : Expr} {as : List Action} :
  ActionsDisjoint (.expr e :: as) ↔ e.Disjoint ∧ ActionsDisjoint as := by
  rfl

@[simp] theorem actionsDisjoint_closeGroup {tag : Nat} {as : List Action} :
  ActionsDisjoint (.closeGroup tag :: as) ↔ ActionsDisjoint as := by
  rfl

@[simp] theorem actionsDisjoint_single_expr {e : Expr} :
  ActionsDisjoint [.expr e] ↔ e.Disjoint := by
  simp [ActionsDisjoint]

@[simp] theorem actionsDisjoint_group_expr_closeGroup {tag : Nat} {e : Expr} {as : List Action} :
  ActionsDisjoint (.expr (.group tag e) :: as) ↔
    tag ∉ e.tags ∧ ActionsDisjoint (.expr e :: .closeGroup tag :: as) := by
  simp [Expr.Disjoint, and_assoc, and_left_comm, and_comm]

@[simp] theorem actionsDisjoint_alternate_branches {e₁ e₂ : Expr} {as : List Action} :
  ActionsDisjoint (.expr (.alternate e₁ e₂) :: as) ↔
    ActionsDisjoint (.expr e₁ :: as) ∧ ActionsDisjoint (.expr e₂ :: as) := by
  simp [Expr.Disjoint, and_assoc, and_left_comm, and_comm]

@[simp] theorem actionsDisjoint_concat_exprs {e₁ e₂ : Expr} {as : List Action} :
  ActionsDisjoint (.expr (.concat e₁ e₂) :: as) ↔
    ActionsDisjoint (.expr e₁ :: .expr e₂ :: as) := by
  simp [Expr.Disjoint, and_assoc]

@[simp] theorem actionsDisjoint_star_unfold {greedy : Bool} {e : Expr} {as : List Action} :
  ActionsDisjoint (.expr (.star greedy e) :: as) ↔
    ActionsDisjoint (.expr e :: .expr (.star greedy e) :: as) := by
  simp [Expr.Disjoint]

inductive Runs {s : String} : List Action → Pos s → GroupMap s → Pos s → GroupMap s → Prop where
  | nil {p : Pos s} {gs : GroupMap s} :
    Runs [] p gs p gs
  | expr {e : Expr} {as : List Action} {p p' q : Pos s} {gs gs' : GroupMap s} {groups : CaptureGroups s}
    (cap : e.Captures p p' groups) (rest : Runs as p' (gs.addCaptures groups) q gs') :
    Runs (.expr e :: as) p gs q gs'
  | closeGroup {tag : Nat} {as : List Action} {p q : Pos s} {gs gs' : GroupMap s}
    (rest : Runs as p (gs.closeGroup tag p) q gs') :
    Runs (.closeGroup tag :: as) p gs q gs'

namespace Runs

theorem head_expr {s : String} {e : Expr} {as : List Action} {p q : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.expr e :: as) p gs q gs') :
  ∃ p' groups, e.Captures p p' groups ∧ Runs as p' (gs.addCaptures groups) q gs' := by
  cases h with
  | expr cap rest => exact ⟨_, _, cap, rest⟩

theorem head_closeGroup {s : String} {tag : Nat} {as : List Action} {p q : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.closeGroup tag :: as) p gs q gs') :
  Runs as p (gs.closeGroup tag p) q gs' := by
  cases h with
  | closeGroup rest => exact rest

theorem head_expr_expr {s : String} {e₁ e₂ : Expr} {as : List Action} {p q : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.expr e₁ :: .expr e₂ :: as) p gs q gs') :
  ∃ p' p'' groups₁ groups₂,
    e₁.Captures p p' groups₁ ∧
    e₂.Captures p' p'' groups₂ ∧
    Runs as p'' ((gs.addCaptures groups₁).addCaptures groups₂) q gs' := by
  obtain ⟨p', groups₁, cap₁, hrest₁⟩ := Runs.head_expr h
  obtain ⟨p'', groups₂, cap₂, hrest₂⟩ := Runs.head_expr hrest₁
  exact ⟨p', p'', groups₁, groups₂, cap₁, cap₂, hrest₂⟩

end Runs

theorem mem_extractCapturesAux_of_runs {s : String} {as : List Action}
  {p₁ p₂ : Pos s} {gs gs' : GroupMap s} {t : BacktrackingTree}
  (v : t.IsValid as p₁ gs) (hdisj : ActionsDisjoint as) (r : Runs as p₁ gs p₂ gs') :
  (p₂, gs') ∈ t.extractCapturesAux p₁ gs := by
  induction v generalizing p₂ gs' with
  | complete =>
    cases r
    simp [extractCapturesAux]
  | epsilon h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | epsilon =>
        exact ih (actionsDisjoint_expr.mp hdisj).2 rest
  | anchor ha h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | anchor htest =>
        exact ih (actionsDisjoint_expr.mp hdisj).2 rest
  | anchorFail ha =>
    cases r with
    | expr cap rest =>
      cases cap with
      | anchor htest => grind
  | char hp hc h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | char hp' hc' =>
        simpa [extractCapturesAux, hp] using ih (actionsDisjoint_expr.mp hdisj).2 rest
  | @charFail c as p gs hp =>
    cases r with
    | expr cap rest =>
      cases cap with
      | char hp' hc' => grind
  | sparse hp hc h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | sparse hp' hc' =>
        simpa [extractCapturesAux, hp] using ih (actionsDisjoint_expr.mp hdisj).2 rest
  | @sparseFail cs as p gs hp =>
    cases r with
    | expr cap rest =>
      cases cap with
      | sparse hp' hc' => grind
  | @openGroup tag e as p gs t h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | group capInner =>
        rename_i pmid groups
        have ⟨htag, hprem⟩ := actionsDisjoint_group_expr_closeGroup.mp hdisj
        have hclose :
            ((gs.openGroup tag p).addCaptures groups).closeGroup tag pmid =
              gs.addCaptures (.group tag p pmid groups) := by
          apply GroupMap.closeGroup_addCaptures_openGroup_eq_addCaptures_group
          intro first last mem
          exact htag (capInner.mem_tags_of_mem_groups _ _ _ mem)
        have hrest' : Runs as pmid (((gs.openGroup tag p).addCaptures groups).closeGroup tag pmid) p₂ gs' := by
          simpa [hclose] using rest
        have hinner : Runs (.expr e :: .closeGroup tag :: as) p (gs.openGroup tag p) p₂ gs' :=
          .expr capInner (.closeGroup hrest')
        simpa [extractCapturesAux] using ih hprem hinner
  | closeGroup h ih =>
    cases r with
    | closeGroup r =>
      simpa [extractCapturesAux] using ih (actionsDisjoint_closeGroup.mp hdisj) r
  | @alternate e₁ e₂ as p gs t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    cases r with
    | expr cap rest =>
      have ⟨hleft, hright⟩ := actionsDisjoint_alternate_branches.mp hdisj
      cases cap with
      | alternateLeft capLeft =>
        exact List.mem_append.mpr <| Or.inl <| ih₁ hleft (.expr capLeft rest)
      | alternateRight capRight =>
        exact List.mem_append.mpr <| Or.inr <| ih₂ hright (.expr capRight rest)
  | @concat e₁ e₂ as p gs t h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | @concat p p' p'' groups₁ groups₂ e₁ e₂ cap₁ cap₂ =>
        have hprem := actionsDisjoint_concat_exprs.mp hdisj
        have hrest' : Runs (.expr e₂ :: as) p' (gs.addCaptures groups₁) p₂ gs' :=
          .expr cap₂ (by simpa [GroupMap.addCaptures] using rest)
        exact ih hprem (.expr cap₁ hrest')
  | @star greedy e as p gs tLoop tExit h₁ h₂ ih₁ ih₂ =>
    cases r with
    | expr cap rest =>
      have hprem := actionsDisjoint_star_unfold.mp hdisj
      have htail := (actionsDisjoint_expr.mp hdisj).2
      cases cap with
      | starEpsilon =>
        cases greedy
        · exact List.mem_append.mpr <| Or.inl <| ih₂ htail rest
        · exact List.mem_append.mpr <| Or.inr <| ih₂ htail rest
      | @starConcat p p' p'' groups₁ groups₂ _ _ cap₁ cap₂ =>
        have hrest' : Runs (.expr (.star greedy e) :: as) p' (gs.addCaptures groups₁) p₂ gs' :=
          .expr cap₂ (by simpa [GroupMap.addCaptures] using rest)
        cases greedy
        · exact List.mem_append.mpr <| Or.inr <| ih₁ hprem (.expr cap₁ hrest')
        · exact List.mem_append.mpr <| Or.inl <| ih₁ hprem (.expr cap₁ hrest')

theorem runs_of_mem_extractCapturesAux {s : String} {as : List Action}
  {p₁ p₂ : Pos s} {gs gs' : GroupMap s} {t : BacktrackingTree}
  (v : t.IsValid as p₁ gs) (hdisj : ActionsDisjoint as) (hmem : (p₂, gs') ∈ t.extractCapturesAux p₁ gs) :
  Runs as p₁ gs p₂ gs' := by
  induction v generalizing p₂ gs' with
  | complete =>
    simp [BacktrackingTree.extractCapturesAux] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact .nil
  | epsilon hvalid ih =>
    exact .expr .epsilon (ih (actionsDisjoint_expr.mp hdisj).2 hmem)
  | anchor ha hvalid ih =>
    exact .expr (.anchor ha) (ih (actionsDisjoint_expr.mp hdisj).2 hmem)
  | anchorFail ha =>
    simp [BacktrackingTree.extractCapturesAux] at hmem
  | char hp hc hvalid ih =>
    simp [BacktrackingTree.extractCapturesAux, hp] at hmem
    exact .expr (.char hp hc) (ih (actionsDisjoint_expr.mp hdisj).2 hmem)
  | charFail hp =>
    simp [BacktrackingTree.extractCapturesAux] at hmem
  | sparse hp hc hvalid ih =>
    simp [BacktrackingTree.extractCapturesAux, hp] at hmem
    exact .expr (.sparse hp hc) (ih (actionsDisjoint_expr.mp hdisj).2 hmem)
  | sparseFail hp =>
    simp [BacktrackingTree.extractCapturesAux] at hmem
  | @openGroup tag e as p gs t hvalid ih =>
    have ⟨htag, hprem⟩ := actionsDisjoint_group_expr_closeGroup.mp hdisj
    have hinner := ih hprem (by simpa [extractCapturesAux] using hmem)
    obtain ⟨pEnd, groups, capInner, hrest₀⟩ := Runs.head_expr hinner
    have hrest := Runs.head_closeGroup hrest₀
    have hclose :
        ((gs.openGroup tag p).addCaptures groups).closeGroup tag pEnd =
          gs.addCaptures (.group tag p pEnd groups) := by
      apply GroupMap.closeGroup_addCaptures_openGroup_eq_addCaptures_group
      intro first last mem
      exact htag (capInner.mem_tags_of_mem_groups _ _ _ mem)
    exact .expr (.group capInner) (by simpa [hclose] using hrest)
  | closeGroup hvalid ih =>
    exact .closeGroup (ih (actionsDisjoint_closeGroup.mp hdisj) (by simpa [extractCapturesAux] using hmem))
  | @alternate e₁ e₂ as p gs t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    simp [BacktrackingTree.extractCapturesAux] at hmem
    rcases hmem with hmem | hmem
    · have hhead : (Expr.alternate e₁ e₂).Disjoint := (actionsDisjoint_expr.mp hdisj).1
      have ⟨hleft, _⟩ := actionsDisjoint_alternate_branches.mp hdisj
      obtain ⟨p', groups, capLeft, hrest⟩ := Runs.head_expr (ih₁ hleft hmem)
      exact .expr (.alternateLeft capLeft) hrest
    · have hhead : (Expr.alternate e₁ e₂).Disjoint := (actionsDisjoint_expr.mp hdisj).1
      have ⟨_, hright⟩ := actionsDisjoint_alternate_branches.mp hdisj
      obtain ⟨p', groups, capRight, hrest⟩ := Runs.head_expr (ih₂ hright hmem)
      exact .expr (.alternateRight capRight) hrest
  | @concat e₁ e₂ as p gs t hvalid ih =>
    have hprem := actionsDisjoint_concat_exprs.mp hdisj
    have hinner := ih hprem hmem
    obtain ⟨p', p'', groups₁, groups₂, cap₁, cap₂, hrest₂⟩ := Runs.head_expr_expr hinner
    exact .expr (.concat cap₁ cap₂) (by simpa [GroupMap.addCaptures] using hrest₂)
  | @star greedy e as p gs tLoop tExit h₁ h₂ ih₁ ih₂ =>
    have htail := (actionsDisjoint_expr.mp hdisj).2
    have hprem := actionsDisjoint_star_unfold.mp hdisj
    have hExit (hmem : (p₂, gs') ∈ tExit.extractCapturesAux p gs) :
      Runs (.expr (.star greedy e) :: as) p gs p₂ gs' := by
      exact .expr .starEpsilon (ih₂ htail (by simpa [extractCapturesAux] using hmem))
    have hLoop (hmem : (p₂, gs') ∈ tLoop.extractCapturesAux p gs) :
      Runs (.expr (.star greedy e) :: as) p gs p₂ gs' := by
      have hinner := ih₁ hprem hmem
      obtain ⟨p', p'', groups₁, groups₂, cap₁, cap₂, hrest₂⟩ := Runs.head_expr_expr hinner
      exact .expr (.starConcat cap₁ cap₂) (by simpa [GroupMap.addCaptures] using hrest₂)
    grind [BacktrackingTree.extractCapturesAux]

theorem mem_extractCapturesAux_of_captures {s : String} {p₁ p₂ p₃ : Pos s}
  {groups : CaptureGroups s} {e : Expr} {as : List Action}
  {gs gs' : GroupMap s} {t : BacktrackingTree}
  (v : t.IsValid (.expr e :: as) p₁ gs) (hdisj : ActionsDisjoint (.expr e :: as)) (c : e.Captures p₁ p₂ groups)
  (r : Runs as p₂ (gs.addCaptures groups) p₃ gs') :
  (p₃, gs') ∈ t.extractCapturesAux p₁ gs :=
  mem_extractCapturesAux_of_runs v hdisj (.expr c r)

theorem captures_of_mem_extractCapturesAux {s : String} {p₁ p₃ : Pos s}
  {gs gs' : GroupMap s} {e : Expr} {as : List Action} {t : BacktrackingTree}
  (v : t.IsValid (.expr e :: as) p₁ gs)
  (hmem : (p₃, gs') ∈ t.extractCapturesAux p₁ gs)
  (hdisj : ActionsDisjoint (.expr e :: as)) :
  ∃ p₂ groups, e.Captures p₁ p₂ groups ∧ Runs as p₂ (gs.addCaptures groups) p₃ gs' :=
  Runs.head_expr (runs_of_mem_extractCapturesAux v hdisj hmem)

public theorem mem_extractCaptures_of_captures {s : String} {p p' : Pos s} {groups : CaptureGroups s} {e : Expr}
  {t : BacktrackingTree}
  (v : t.IsValid [.expr e] p .empty) (disj : e.Disjoint) (c : e.Captures p p' groups) :
  (p', GroupMap.addCaptures GroupMap.empty groups) ∈ t.extractCaptures p :=
  mem_extractCapturesAux_of_captures v ⟨disj, trivial⟩ c Runs.nil

public theorem captures_of_mem_extractCaptures {s : String} {p p' : Pos s} {gs : GroupMap s} {e : Expr}
  {t : BacktrackingTree}
  (v : t.IsValid [.expr e] p .empty) (hmem : (p', gs) ∈ t.extractCaptures p) (disj : e.Disjoint) :
  ∃ groups, e.Captures p p' groups ∧ gs = GroupMap.addCaptures GroupMap.empty groups := by
  have hdisj : ActionsDisjoint [.expr e] := by
    exact ⟨disj, trivial⟩
  obtain ⟨p₂, groups, cap, r⟩ :=
    captures_of_mem_extractCapturesAux v (by simpa [BacktrackingTree.extractCaptures] using hmem) hdisj
  cases r with
  | nil =>
    exact ⟨groups, cap, rfl⟩

end Regex.Data.Expr.BacktrackingTree
