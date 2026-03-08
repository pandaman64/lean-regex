module

public import Regex.Data.Expr
public import RegexCorrectness.Data.Expr.Semantics.Captures
public import RegexCorrectness.Data.Expr.Semantics.Separation
public import RegexCorrectness.Data.Expr.Semantics.GroupMap

open String (Pos)

public section

namespace Regex.Data.Expr

/--
`BacktrackingTree` records the full backtracking search traces of a regex match.

Leaves represent success or failure, and internal nodes represent the operational effects of
backtracking evaluation such as branching, reading one character, checking an anchor, and opening
or closing a capture group.

Reference: Barriere, Deng, and Pit-Claudel, "Formal Verification for JavaScript Regular
Expressions: a Proven Semantics and its Applications (Extended Version)",
https://arxiv.org/abs/2507.13091
-/
inductive BacktrackingTree where
  | complete
  | fail
  | choice (t₁ t₂ : BacktrackingTree)
  | read (next : BacktrackingTree)
  | anchorPass (next : BacktrackingTree)
  | openGroup (tag : Nat) (next : BacktrackingTree)
  | closeGroup (tag : Nat) (next : BacktrackingTree)
deriving Inhabited

namespace BacktrackingTree

variable {s : String}

inductive Action where
  | expr (e : Expr)
  | closeGroup (tag : Nat)

inductive IsValid {s : String} : List Action → Pos s → GroupMap s → BacktrackingTree → Prop where
  | complete {p : Pos s} {gs : GroupMap s} :
    IsValid [] p gs .complete
  | epsilon {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree} (h : IsValid as p gs t) :
    IsValid (.expr .epsilon :: as) p gs t
  | anchor {a : Anchor} {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree}
    (ha : a.test p) (h : IsValid as p gs t) :
    IsValid (.expr (.anchor a) :: as) p gs (.anchorPass t)
  | anchorFail {a : Anchor} {as : List Action} {p : Pos s} {gs : GroupMap s} (ha : ¬a.test p) :
    IsValid (.expr (.anchor a) :: as) p gs .fail
  | char {c : Char} {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree}
    (hp : p ≠ s.endPos) (hc : p.get hp = c) (h : IsValid as (p.next hp) gs t) :
    IsValid (.expr (.char c) :: as) p gs (.read t)
  | charFail {c : Char} {as : List Action} {p : Pos s} {gs : GroupMap s}
    (hp : p = s.endPos ∨ ∃ hp' : p ≠ s.endPos, p.get hp' ≠ c) :
    IsValid (.expr (.char c) :: as) p gs .fail
  | sparse {cs : Classes} {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree}
    (hp : p ≠ s.endPos) (hc : p.get hp ∈ cs) (h : IsValid as (p.next hp) gs t) :
    IsValid (.expr (.classes cs) :: as) p gs (.read t)
  | sparseFail {cs : Classes} {as : List Action} {p : Pos s} {gs : GroupMap s}
    (hp : p = s.endPos ∨ ∃ hp' : p ≠ s.endPos, p.get hp' ∉ cs) :
    IsValid (.expr (.classes cs) :: as) p gs .fail
  | openGroup {tag : Nat} {e : Expr} {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree}
    (h : IsValid (.expr e :: .closeGroup tag :: as) p (gs.openGroup tag p) t) :
    IsValid (.expr (.group tag e) :: as) p gs (.openGroup tag t)
  | closeGroup {tag : Nat} {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree}
    (h : IsValid as p (gs.closeGroup tag p) t) :
    IsValid (.closeGroup tag :: as) p gs (.closeGroup tag t)
  | alternate {e₁ e₂ : Expr} {as : List Action} {p : Pos s} {gs : GroupMap s} {t₁ t₂ : BacktrackingTree}
    (h₁ : IsValid (.expr e₁ :: as) p gs t₁) (h₂ : IsValid (.expr e₂ :: as) p gs t₂) :
    IsValid (.expr (.alternate e₁ e₂) :: as) p gs (.choice t₁ t₂)
  | concat {e₁ e₂ : Expr} {as : List Action} {p : Pos s} {gs : GroupMap s} {t : BacktrackingTree}
    (h : IsValid (.expr e₁ :: .expr e₂ :: as) p gs t) :
    IsValid (.expr (.concat e₁ e₂) :: as) p gs t
  -- TODO: empty checking
  | star {greedy : Bool} {e : Expr} {as : List Action} {p : Pos s} {gs : GroupMap s}
    {tLoop tExit : BacktrackingTree}
    (h₁ : IsValid (.expr e :: .expr (.star greedy e) :: as) p gs tLoop)
    (h₂ : IsValid as p gs tExit) :
    IsValid (.expr (.star greedy e) :: as) p gs
      (if greedy then .choice tLoop tExit else .choice tExit tLoop)

theorem deterministic_isValid {s : String} {as : List Action} {p : Pos s} {gs : GroupMap s} {t₁ t₂ : BacktrackingTree}
  (h₁ : IsValid as p gs t₁) (h₂ : IsValid as p gs t₂) :
  t₁ = t₂ := by
  induction h₁ generalizing t₂ <;> grind [IsValid]

def firstMatch (t : BacktrackingTree) : Option Unit :=
  match t with
  | .complete => .some ()
  | .fail => .none
  | .choice t₁ t₂ => firstMatch t₁ <|> firstMatch t₂
  | .read t => t.firstMatch
  | .anchorPass t => t.firstMatch
  | .openGroup _ t => t.firstMatch
  | .closeGroup _ t => t.firstMatch

def extractCapturesAux {s : String} (p : Pos s) (gs : GroupMap s) (t : BacktrackingTree) : List (Pos s × GroupMap s) :=
  match t with
  | .complete => [(p, gs)]
  | .fail => []
  | .choice t₁ t₂ => t₁.extractCapturesAux p gs ++ t₂.extractCapturesAux p gs
  | .read t => if hp : p ≠ s.endPos then t.extractCapturesAux (p.next hp) gs else []
  | .anchorPass t => t.extractCapturesAux p gs
  | .openGroup tag t => t.extractCapturesAux p (gs.openGroup tag p)
  | .closeGroup tag t => t.extractCapturesAux p (gs.closeGroup tag p)

def extractCaptures {s : String} (startAt : Pos s) (t : BacktrackingTree) : List (Pos s × GroupMap s) :=
  t.extractCapturesAux startAt .empty

end BacktrackingTree

end Regex.Data.Expr

end
