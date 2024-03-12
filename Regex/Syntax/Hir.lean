import Regex.Regex

namespace Regex.Syntax.Parser

private def MAX_UNICODE : Nat := 0x10FFFF

private def invertIntervals (int: Array (Char × Char)) : Array (Char × Char) := Id.run do
  let intervals := int.qsort (λ a b => a.1 < b.1)
  let mut result := #[]
  let mut lastEnd : Int := (-1)

  for interval in intervals do
    let start := interval.1.toNat
    let end_ := interval.2.toNat
    if start > lastEnd + 1 then
      result := result.push (Char.ofNat (lastEnd + 1).toNat, Char.ofNat (start - 1))
    lastEnd := if end_ > lastEnd then end_ else lastEnd

  if lastEnd < MAX_UNICODE then
    result := result.push (Char.ofNat (lastEnd + 1).toNat, Char.ofNat MAX_UNICODE)

  return result

private def mergeIntervals (int: Array (Char × Char)) : Array (Char × Char) := Id.run do
  let intervals := int.qsort (λ a b => a.1 < b.1)
  let mut merged := #[]

  for interval in intervals do
    if merged.isEmpty || interval.fst > merged.back.snd then
      merged := merged.push interval
    else
      let snd := Char.ofNat $ Nat.max merged[merged.size-1]!.snd.toNat interval.snd.toNat
      merged  := merged.set! (merged.size - 1) (merged[merged.size-1]!.fst, snd)

  return merged

inductive PerlClassKind where
  | digit
  | space
  | word
  deriving Repr

def PerlClassKind.toRange : PerlClassKind → Array (Char × Char)
  | .digit => #[('0', '9')]
  | .space => #[(' ', ' '), ('\t', '\t'), ('\n', '\n'), ('\r', '\r'), ('\x0B', '\x0B'), ('\x0C', '\x0C')]
  | .word => #[('a', 'z'), ('A', 'Z'), ('0', '9'), ('_', '_')]

structure PerlClass where
  negated: Bool
  kind: PerlClassKind
  deriving Repr

def PerlClass.toRange (perl: PerlClass) : Array (Char × Char) :=
  if perl.negated
    then invertIntervals perl.kind.toRange
    else perl.kind.toRange

inductive Interval where
  | single : Char → Interval
  | range : Char → Char → Interval
  | perl : PerlClass → Interval
  deriving Repr

def Interval.toRange : Interval → Array (Char × Char)
  | .single c    => #[(c, c)]
  | .range c₁ c₂ => #[(c₁, c₂)]
  | .perl p      => p.toRange

structure Classes where
  negated: Bool
  intervals: Array Interval
  deriving Repr

def Classes.toRange (classes: Classes) : Array (Char × Char) :=
  let intervals := Array.concatMap (·.toRange) classes.intervals

  let intervals₁ := if classes.negated
    then invertIntervals intervals
    else intervals

  mergeIntervals intervals₁

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
deriving Repr, Inhabited

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
  | .dot => (index, .classes #[(Char.ofNat 0, Char.ofNat MAX_UNICODE)])

def Hir.toRegex (h : Hir) : Regex := (h.toRegexAux 0).2

end Regex.Syntax.Parser
