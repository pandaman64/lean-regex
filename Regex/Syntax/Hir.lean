import Regex.Regex
import Regex.Intervals

namespace Regex.Syntax.Parser

inductive PerlClassKind where
  | digit
  | space
  | word
  deriving Repr

def PerlClassKind.toRange : PerlClassKind → Intervals
  | .digit => #[⟨('0', '9'), by decide⟩]
  | .space => #[⟨(' ', ' '), by decide⟩, ⟨('\t', '\t'), by decide⟩, ⟨('\n', '\n'), by decide⟩, ⟨('\r', '\r'), by decide⟩, ⟨('\x0B', '\x0B'), by decide⟩, ⟨('\x0C', '\x0C'), by decide⟩]
  | .word => #[⟨('a', 'z'), by decide⟩, ⟨('A', 'Z'), by decide⟩, ⟨('0', '9'), by decide⟩, ⟨('_', '_'), by decide⟩]

structure PerlClass where
  negated: Bool
  kind: PerlClassKind
  deriving Repr

def PerlClass.toRange (perl: PerlClass) : Intervals :=
  if perl.negated
    then Intervals.invert perl.kind.toRange
    else perl.kind.toRange

inductive Interval where
  | single : Char → Interval
  | range : (s : Char) → (e : Char) → s ≤ e → Interval
  | perl : PerlClass → Interval

def Interval.toRange : Interval → Intervals
  | .single c      => #[⟨(c, c), by simp⟩]
  | .range c₁ c₂ r => #[⟨(c₁, c₂), r⟩]
  | .perl p        => p.toRange

structure Classes where
  negated: Bool
  intervals: Array Interval

def Classes.toRange (classes: Classes) : Intervals :=
  let intervals := Array.concatMap (·.toRange) classes.intervals

  let intervals₁ : Intervals := if classes.negated
    then Intervals.invert intervals
    else intervals

  Intervals.merge intervals₁

inductive Hir : Type where
  | empty : Hir
  | epsilon : Hir
  | char : Char → Hir
  | group : Hir → Hir
  | alternate : Hir → Hir → Hir
  | concat : Hir → Hir → Hir
  | star : Hir → Hir
  | classes : Classes -> Hir
  | perl : PerlClass -> Hir
  | dot : Hir
deriving Inhabited

def Hir.toRegexAux (index : Nat) (hir : Hir) : Nat × Regex :=
  match hir with
  | .empty => (index, .empty)
  | .epsilon => (index, .epsilon)
  | .char c => (index, .char c)
  | .group h =>
    let (index', r) := h.toRegexAux (index + 1)
    (index', .group index r)
  | .alternate h₁ h₂ =>
    let (index₁, r₁) := h₁.toRegexAux index
    let (index₂, r₂) := h₂.toRegexAux index₁
    (index₂, .alternate r₁ r₂)
  | .concat h₁ h₂ =>
    let (index₁, r₁) := h₁.toRegexAux index
    let (index₂, r₂) := h₂.toRegexAux index₁
    (index₂, .concat r₁ r₂)
  | .star h =>
    let (index', r) := h.toRegexAux index
    (index', .star r)
  | .classes c =>
    (index, .classes c.toRange)
  | .perl p =>
    (index, .classes p.toRange)
  | .dot => (index, .classes #[⟨(Char.ofNat 0, Char.ofNat Char.MAX_UNICODE), by decide⟩])

def Hir.toRegex (h : Hir) : Regex := (h.toRegexAux 0).2

end Regex.Syntax.Parser
