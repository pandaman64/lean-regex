module

public import RegexCorrectness.Data.Expr.Semantics.Tree.Basic
import all RegexCorrectness.Data.Expr.Semantics.Tree.Basic
public import RegexCorrectness.Data.Expr.Nullable

open String (Pos)

namespace Regex.Data.Expr.Semantics.Tree

variable {s : String}

def WfActions : List (Action s) → Prop
  | [] => True
  | .expr e :: as => e.Disjoint ∧ ¬e.NullableStar ∧ WfActions as
  | .closeGroup _ :: as => WfActions as
  | .check _ :: as => WfActions as

@[simp] theorem wfActions_expr {e : Expr} {as : List (Action s)} :
  WfActions (.expr e :: as) ↔ e.Disjoint ∧ ¬e.NullableStar ∧ WfActions as := by
  rfl

@[simp] theorem wfActions_closeGroup {tag : Nat} {as : List (Action s)} :
  WfActions (.closeGroup tag :: as) ↔ WfActions as := by
  rfl

@[simp] theorem wfActions_check {p : Pos s} {as : List (Action s)} :
  WfActions (.check p :: as) ↔ WfActions as := by
  rfl

@[simp] theorem wfActions_single_expr {e : Expr} :
  WfActions (s := s) [.expr e] ↔ e.Disjoint ∧ ¬e.NullableStar := by
  simp [WfActions]

@[simp] theorem wfActions_group_expr_closeGroup {tag : Nat} {e : Expr} {as : List (Action s)} :
  WfActions (.expr (.group tag e) :: as) ↔
    tag ∉ e.tags ∧ ¬e.NullableStar ∧ WfActions (.expr e :: .closeGroup tag :: as) := by
  simp [Disjoint, NullableStar, and_assoc, and_left_comm, and_comm]

@[simp] theorem wfActions_alternate_branches {e₁ e₂ : Expr} {as : List (Action s)} :
  WfActions (.expr (.alternate e₁ e₂) :: as) ↔
    WfActions (.expr e₁ :: as) ∧ WfActions (.expr e₂ :: as) := by
  simp [Disjoint, NullableStar, and_assoc, and_left_comm, and_comm]

@[simp] theorem wfActions_concat_exprs {e₁ e₂ : Expr} {as : List (Action s)} :
  WfActions (.expr (.concat e₁ e₂) :: as) ↔
    WfActions (.expr e₁ :: .expr e₂ :: as) := by
  grind [Disjoint, wfActions_expr]

@[simp] theorem wfActions_star_unfold {greedy : Bool} {e : Expr} {as : List (Action s)} :
  WfActions (.expr (.star greedy e) :: as) ↔
    WfActions (.expr e :: .expr (.star greedy e) :: as) := by
  grind [Disjoint, wfActions_expr]

inductive Runs {s : String} : List (Action s) → Pos s → GroupMap s → Pos s → GroupMap s → Prop where
  | nil {p : Pos s} {gs : GroupMap s} :
    Runs [] p gs p gs
  | expr {e : Expr} {as : List (Action s)} {p p' q : Pos s} {gs gs' : GroupMap s} {groups : CaptureGroups s}
    (cap : e.Captures p p' groups) (rest : Runs as p' (gs.addCaptures groups) q gs') :
    Runs (.expr e :: as) p gs q gs'
  | closeGroup {tag : Nat} {as : List (Action s)} {p q : Pos s} {gs gs' : GroupMap s}
    (rest : Runs as p (gs.closeGroup tag p) q gs') :
    Runs (.closeGroup tag :: as) p gs q gs'
  | check {as : List (Action s)} {pc p q : Pos s} {gs gs' : GroupMap s}
    (h : pc < p) (rest : Runs as p gs q gs') :
    Runs (.check pc :: as) p gs q gs'

namespace Runs

theorem head_expr {e : Expr} {as : List (Action s)} {p q : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.expr e :: as) p gs q gs') :
  ∃ p' groups, e.Captures p p' groups ∧ Runs as p' (gs.addCaptures groups) q gs' := by
  cases h with
  | expr cap rest => exact ⟨_, _, cap, rest⟩

theorem head_closeGroup {tag : Nat} {as : List (Action s)} {p q : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.closeGroup tag :: as) p gs q gs') :
  Runs as p (gs.closeGroup tag p) q gs' := by
  cases h with
  | closeGroup rest => exact rest

theorem head_check {pc : Pos s} {as : List (Action s)} {p p' : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.check pc :: as) p gs p' gs') :
  pc < p ∧ Runs as p gs p' gs' := by
  cases h with
  | check hpc hrest => exact ⟨hpc, hrest⟩

theorem head_expr_expr {e₁ e₂ : Expr} {as : List (Action s)} {p q : Pos s} {gs gs' : GroupMap s}
  (h : Runs (.expr e₁ :: .expr e₂ :: as) p gs q gs') :
  ∃ p' p'' groups₁ groups₂,
    e₁.Captures p p' groups₁ ∧
    e₂.Captures p' p'' groups₂ ∧
    Runs as p'' ((gs.addCaptures groups₁).addCaptures groups₂) q gs' := by
  obtain ⟨p', groups₁, cap₁, hrest₁⟩ := Runs.head_expr h
  obtain ⟨p'', groups₂, cap₂, hrest₂⟩ := Runs.head_expr hrest₁
  exact ⟨p', p'', groups₁, groups₂, cap₁, cap₂, hrest₂⟩

end Runs

theorem mem_extractCapturesAux_of_runs {as : List (Action s)}
  {p₁ p₂ : Pos s} {gs gs' : GroupMap s} {t : Tree}
  (v : t.IsValid as p₁ gs) (wf : WfActions as) (r : Runs as p₁ gs p₂ gs') :
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
        exact ih (wfActions_expr.mp wf).2.2 rest
  | anchor ha h ih =>
    cases r with
    | expr cap rest =>
      cases cap with
      | anchor htest =>
        exact ih (wfActions_expr.mp wf).2.2 rest
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
        simpa [extractCapturesAux, hp] using ih (wfActions_expr.mp wf).2.2 rest
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
        simpa [extractCapturesAux, hp] using ih (wfActions_expr.mp wf).2.2 rest
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
        have ⟨htag, _, hprem⟩ := wfActions_group_expr_closeGroup.mp wf
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
      simpa [extractCapturesAux] using ih (wfActions_closeGroup.mp wf) r
  | @alternate e₁ e₂ as p gs t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    cases r with
    | expr cap rest =>
      have ⟨hleft, hright⟩ := wfActions_alternate_branches.mp wf
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
        have hprem := wfActions_concat_exprs.mp wf
        have hrest' : Runs (.expr e₂ :: as) p' (gs.addCaptures groups₁) p₂ gs' :=
          .expr cap₂ (by simpa [GroupMap.addCaptures] using rest)
        exact ih hprem (.expr cap₁ hrest')
  | @star greedy e as p gs tLoop tOnce tExit h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    cases r with
    | @expr _ _ _ q _ _ _ groups cap rest =>
      have hprem := wfActions_star_unfold.mp wf
      have ⟨hns, htail⟩ := (wfActions_expr.mp wf).2
      cases cap with
      | starEpsilon =>
        cases greedy
        · exact List.mem_append.mpr <| Or.inl <| ih₃ htail rest
        · exact List.mem_append.mpr <| Or.inr <| ih₃ htail rest
      | @starConcat p p' p'' groups₁ groups₂ _ _ cap₁ cap₂ =>
        have hrest' : Runs (.expr (.star greedy e) :: as) p' (gs.addCaptures groups₁) p₂ gs' :=
          .expr cap₂ (by simpa [GroupMap.addCaptures] using rest)
        have mem : (p₂, gs') ∈ extractCapturesAux p gs tLoop := by
          apply ih₁ ?_ ?_
          . simpa [wfActions_expr, wfActions_check] using hprem
          . simp only [NullableStar, not_or] at hns
            exact .expr cap₁ (.check (cap₁.lt_of_not_nullable hns.1) (.expr cap₂ rest))
        cases greedy
        · exact List.mem_append.mpr <| .inr (List.mem_append.mpr <| .inr mem)
        · exact List.mem_append.mpr <| .inl (List.mem_append.mpr <| .inl mem)
  | @progress as p p' gs t hp h ih =>
    cases r with
    | check h rest =>
      simpa [extractCapturesAux] using ih (wfActions_check.mp wf) rest

theorem runs_of_mem_extractCapturesAux {as : List (Action s)}
  {p₁ p₂ : Pos s} {gs gs' : GroupMap s} {t : Tree}
  (v : t.IsValid as p₁ gs) (wf : WfActions as) (hmem : (p₂, gs') ∈ t.extractCapturesAux p₁ gs) :
  Runs as p₁ gs p₂ gs' := by
  induction v generalizing p₂ gs' with
  | complete =>
    simp [extractCapturesAux] at hmem
    rcases hmem with ⟨rfl, rfl⟩
    exact .nil
  | epsilon hvalid ih =>
    exact .expr .epsilon (ih (wfActions_expr.mp wf).2.2 hmem)
  | anchor ha hvalid ih =>
    exact .expr (.anchor ha) (ih (wfActions_expr.mp wf).2.2 hmem)
  | anchorFail ha =>
    simp [extractCapturesAux] at hmem
  | char hp hc hvalid ih =>
    simp [extractCapturesAux, hp] at hmem
    exact .expr (.char hp hc) (ih (wfActions_expr.mp wf).2.2 hmem)
  | charFail hp =>
    simp [extractCapturesAux] at hmem
  | sparse hp hc hvalid ih =>
    simp [extractCapturesAux, hp] at hmem
    exact .expr (.sparse hp hc) (ih (wfActions_expr.mp wf).2.2 hmem)
  | sparseFail hp =>
    simp [extractCapturesAux] at hmem
  | @openGroup tag e as p gs t hvalid ih =>
    have ⟨htag, _, hprem⟩ := wfActions_group_expr_closeGroup.mp wf
    have hinner := ih hprem (by simpa using hmem)
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
    exact .closeGroup (ih (wfActions_closeGroup.mp wf) (by simpa using hmem))
  | @alternate e₁ e₂ as p gs t₁ t₂ h₁ h₂ ih₁ ih₂ =>
    simp [extractCapturesAux] at hmem
    rcases hmem with hmem | hmem
    · have hhead : (Expr.alternate e₁ e₂).Disjoint := (wfActions_expr.mp wf).1
      have ⟨hleft, _⟩ := wfActions_alternate_branches.mp wf
      obtain ⟨p', groups, capLeft, hrest⟩ := Runs.head_expr (ih₁ hleft hmem)
      exact .expr (.alternateLeft capLeft) hrest
    · have hhead : (Expr.alternate e₁ e₂).Disjoint := (wfActions_expr.mp wf).1
      have ⟨_, hright⟩ := wfActions_alternate_branches.mp wf
      obtain ⟨p', groups, capRight, hrest⟩ := Runs.head_expr (ih₂ hright hmem)
      exact .expr (.alternateRight capRight) hrest
  | @concat e₁ e₂ as p gs t hvalid ih =>
    have hprem := wfActions_concat_exprs.mp wf
    have hinner := ih hprem hmem
    obtain ⟨p', p'', groups₁, groups₂, cap₁, cap₂, hrest₂⟩ := Runs.head_expr_expr hinner
    exact .expr (.concat cap₁ cap₂) (by simpa using hrest₂)
  | @star greedy e as p gs tLoop tOnce tExit h₁ h₂ h₃ ih₁ ih₂ ih₃ =>
    have htail := (wfActions_expr.mp wf)
    have hprem := wfActions_star_unfold.mp wf
    have hExit (hmem : (p₂, gs') ∈ tExit.extractCapturesAux p gs) :
      Runs (.expr (.star greedy e) :: as) p gs p₂ gs' := by
      exact .expr .starEpsilon (ih₃ htail.2.2 (by simpa [extractCapturesAux] using hmem))
    have hOnce (hmem : (p₂, gs') ∈ tOnce.extractCapturesAux p gs) :
      Runs (.expr (.star greedy e) :: as) p gs p₂ gs' := by
      obtain ⟨p₁, groups₁, cap₁, hrest₂⟩ := Runs.head_expr (ih₂ (by simp_all) hmem)
      exact .expr (.starConcat cap₁ .starEpsilon) (by simpa using hrest₂)
    have hLoop (hmem : (p₂, gs') ∈ tLoop.extractCapturesAux p gs) :
      Runs (.expr (.star greedy e) :: as) p gs p₂ gs' := by
      have hinner := ih₁ hprem hmem
      obtain ⟨p₁, groups₁, cap₁, hinner'⟩ := Runs.head_expr hinner
      obtain ⟨_, hinner''⟩ := Runs.head_check hinner'
      obtain ⟨p₂, groups₂, cap₂, hrest₂⟩ := Runs.head_expr hinner''
      exact .expr (.starConcat cap₁ cap₂) (by simpa using hrest₂)
    grind [extractCapturesAux]
  | @progress as p p' gs t hp h ih =>
    have hrest := ih (wfActions_check.mp wf) hmem
    exact .check hp hrest

theorem mem_extractCapturesAux_of_captures {p₁ p₂ p₃ : Pos s}
  {groups : CaptureGroups s} {e : Expr} {as : List (Action s)}
  {gs gs' : GroupMap s} {t : Tree}
  (v : t.IsValid (.expr e :: as) p₁ gs) (wf : WfActions (.expr e :: as)) (c : e.Captures p₁ p₂ groups)
  (r : Runs as p₂ (gs.addCaptures groups) p₃ gs') :
  (p₃, gs') ∈ t.extractCapturesAux p₁ gs :=
  mem_extractCapturesAux_of_runs v wf (.expr c r)

theorem captures_of_mem_extractCapturesAux {p₁ p₃ : Pos s}
  {gs gs' : GroupMap s} {e : Expr} {as : List (Action s)} {t : Tree}
  (v : t.IsValid (.expr e :: as) p₁ gs)
  (hmem : (p₃, gs') ∈ t.extractCapturesAux p₁ gs)
  (hdisj : WfActions (.expr e :: as)) :
  ∃ p₂ groups, e.Captures p₁ p₂ groups ∧ Runs as p₂ (gs.addCaptures groups) p₃ gs' :=
  Runs.head_expr (runs_of_mem_extractCapturesAux v hdisj hmem)

public theorem mem_extractCaptures_of_captures {p p' : Pos s} {groups : CaptureGroups s} {e : Expr}
  {t : Tree}
  (v : t.IsValid [.expr e] p .empty)
  (disj : e.Disjoint) (hns : ¬e.NullableStar) (c : e.Captures p p' groups) :
  (p', GroupMap.addCaptures GroupMap.empty groups) ∈ t.extractCaptures p :=
  mem_extractCapturesAux_of_captures v ⟨disj, hns, trivial⟩ c Runs.nil

public theorem captures_of_mem_extractCaptures {p p' : Pos s} {gs : GroupMap s} {e : Expr}
  {t : Tree}
  (v : t.IsValid [.expr e] p .empty) (hmem : (p', gs) ∈ t.extractCaptures p)
  (disj : e.Disjoint) (hns : ¬e.NullableStar) :
  ∃ groups, e.Captures p p' groups ∧ gs = GroupMap.addCaptures GroupMap.empty groups := by
  have hdisj : WfActions (s := s) [.expr e] := by
    exact ⟨disj, hns, trivial⟩
  obtain ⟨p₂, groups, cap, r⟩ :=
    captures_of_mem_extractCapturesAux v (by simpa [extractCaptures] using hmem) hdisj
  cases r with
  | nil =>
    exact ⟨groups, cap, rfl⟩

end Regex.Data.Expr.Semantics.Tree
