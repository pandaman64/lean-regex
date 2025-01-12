import TParser
import Regex.Syntax.Ast

set_option autoImplicit false

open TParser (SimpleParser Parser Box)
open TParser.Indexed
open TParser.Char
open Regex.Data (PerlClass PerlClassKind Class Classes Expr)

namespace Regex.Syntax.Parser

inductive Error where
  | unexpectedEof
  | unexpectedChar
  | unexpectedEscapedChar (c : Char)
  | unexpectedPerlClass (cls : PerlClass)
  | invalidDigit (c : Char)
  | invalidHexDigit (c : Char)
  | invalidRange (c₁ : Char) (c₂ : Char)
  | invalidRepetition (min : Nat) (max : Nat)
  | perlClassInRange (cls : PerlClass)
  | remainingInput
deriving Repr

def specialCharacters := "[](){}*+?|^$.\\"

def charOrError (c : Char) : All (SimpleParser Error Char) :=
  charOrElse c (throw .unexpectedEof) (throw .unexpectedChar)

def digit : All (SimpleParser Error Nat) :=
  anyCharOrElse (throw .unexpectedEof)
  |>.andBindM fun c =>
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else throw (.invalidDigit c)

def number : All (SimpleParser Error Nat) :=
  Parser.foldl 0 (fun n d => 10 * n + d) digit

def hexDigit : All (SimpleParser Error Nat) :=
  anyCharOrElse (throw .unexpectedEof)
  |>.andBindM fun c =>
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw (.invalidHexDigit c)

-- TODO: commit after '\\'?
def escapedChar : All (SimpleParser Error (Char ⊕ PerlClass)) :=
  charOrError '\\'
  |>.andBindR fun _ => Parser.box $
    (hexX.orElse hexU |>.orElse simple |>.map Sum.inl) |>.orElse (perlClass.map Sum.inr)
where
  simple : All (SimpleParser Error Char) :=
    anyCharOrElse (throw .unexpectedEof)
    |>.andBindM fun c =>
      match c with
      | 'n' => pure '\n'
      | 't' => pure '\t'
      | 'r' => pure '\r'
      | 'a' => pure '\x07'
      | 'f' => pure '\x0c'
      | 'v' => pure '\x0b'
      | '0' => pure '\x00'
      | '-' => pure '-'
      | '\\' => pure '\\'
      | _ => throw (.unexpectedEscapedChar c)
  hexX : All (SimpleParser Error Char) :=
    charOrError 'x'
    |>.andBindR fun _ => Parser.box $
      hexDigit.and hexDigit.box
      |>.map fun (d₁, d₂) => Char.ofNat (16 * d₁ + d₂)
  hexU : All (SimpleParser Error Char) :=
    charOrError 'u'
    |>.andBindR fun _ => Parser.box $
      hexDigit.and (hexDigit.and (hexDigit.and hexDigit.box).box).box
      |>.map fun (d₁, d₂, d₃, d₄) => Char.ofNat (4096 * d₁ + 256 * d₂ + 16 * d₃ + d₄)
  perlClass : All (SimpleParser Error PerlClass) :=
    anyCharOrElse (throw .unexpectedEof)
    |>.andBindM fun c =>
      match c with
      | 'd' => pure (PerlClass.mk false PerlClassKind.digit)
      | 'D' => pure (PerlClass.mk true PerlClassKind.digit)
      | 's' => pure (PerlClass.mk false PerlClassKind.space)
      | 'S' => pure (PerlClass.mk true PerlClassKind.space)
      | 'w' => pure (PerlClass.mk false PerlClassKind.word)
      | 'W' => pure (PerlClass.mk true PerlClassKind.word)
      | _ => throw (.unexpectedEscapedChar c)

def plainChar : All (SimpleParser Error Char) :=
  anyCharOrElse (throw .unexpectedEof)
  |>.andBindM fun c =>
    if specialCharacters.contains c then throw (.unexpectedEscapedChar c)
    else pure c

def classesAux : All (SimpleParser Error Class) :=
  elem
  |>.andOpt (charOrError '-' |>.and elem.box).box
  |>.andBindM fun (c₁, c₂) =>
    match c₁, c₂ with
    | .inl c₁, .none => pure (.single c₁)
    | .inr cls₁, .none => pure (.perl cls₁)
    | .inl c₁, .some (_, .inl c₂) =>
      if le : c₁ ≤ c₂ then
        pure (.range c₁ c₂ le)
      else
        throw (.invalidRange c₁ c₂)
    | .inl _, .some (_, .inr cls) => throw (.perlClassInRange cls)
    | .inr cls₁, .some _ => throw (.perlClassInRange cls₁)
where
  elem : All (SimpleParser Error (Char ⊕ PerlClass)) :=
    escapedChar.orElse (plainChar.map .inl)

def classes : All (SimpleParser Error Ast) :=
  Parser.between (charOrError '[') (charOrError ']').box $ Parser.box $
    charOrError '^'
    |>.optAnd classesBody
    |>.map fun (caret, classes) => .classes ⟨caret.isSome, classes⟩
where
  classesBody : All (SimpleParser Error (Array Class)) :=
    Parser.foldl #[] (fun accum cls => accum.push cls) classesAux

def group : All (Imp (Box (SimpleParser Error Ast)) (SimpleParser Error Ast))
  | _, regex =>
    Parser.between' ((charOrError '(').andOpt nonCapturing.box) (charOrError ')').box regex
    |>.map fun ((_, nc), ast, _) =>
      if nc.isSome then
        ast
      else
        .group ast
where
  nonCapturing : All (SimpleParser Error Unit) :=
    charOrError '?' |>.and (charOrError ':').box
    |>.map fun _ => ()

def primary : All (Imp (Box (SimpleParser Error Ast)) (SimpleParser Error Ast))
  | _, regex =>
    group regex
    |>.orElse classes
    |>.orElse (escapedChar.map escapedCharToAst)
    |>.orElse (plainChar.map .char)
where
  escapedCharToAst (c : Char ⊕ PerlClass) : Ast :=
    match c with
    | .inl c => .char c
    | .inr cls => .perl cls

def repetition : All (Imp (Box (SimpleParser Error Ast)) (SimpleParser Error Ast))
  | _, regex => Parser.iteratel (primary regex) (repetitionOp.map fun (min, max) => applyRepetition min max).box
where
  applyRepetition (min : Nat) (max : Option Nat) (ast : Ast) : Ast :=
    match min, max with
    -- special case for well-known repetitions
    | 0, .some 1 => Ast.alternate ast Ast.empty
    | 0, .none => Ast.star ast
    | 1, .none => Ast.concat ast (Ast.star ast)
    -- r{min,}. min > 0 as `0, .none` is already covered.
    | min, .none => Ast.concat (repeatConcat ast (min - 1)) (Ast.star ast)
    -- r{0,max}
    | 0, .some max =>
      if max == 0 then
        Ast.empty
      else
        repeatConcat (Ast.alternate ast Ast.empty) (max - 1)
    -- r{min,max} (min > 0)
    | min, .some max =>
      if min == max then
        repeatConcat ast (min - 1)
      else
        Ast.concat (repeatConcat ast (min - 1)) (repeatConcat (Ast.alternate ast Ast.empty) (max - min - 1))
  repeatConcat (ast : Ast) : Nat → Ast
    | 0 => ast
    | n + 1 => .concat (repeatConcat ast n) ast
  repetitionOp : All (SimpleParser Error (Nat × Option Nat)) :=
    ((charOrError '*').mapConst (0, none))
    |>.orElse ((charOrError '+').mapConst (1, none))
    |>.orElse ((charOrError '?').mapConst (0, some 1))
    |>.orElse (Parser.between (charOrError '{') (charOrError '}').box $ Parser.box $
      number.andOpt (charOrError ',' |>.andOpt number.box).box
      |>.andBindM fun (min, max) =>
        match max with
        | .none => pure (min, .some min) -- {min}
        | .some (_, .none) => pure (min, .none) -- {min,}
        | .some (_, .some max) =>
          if min ≤ max then
            pure (min, .some max) -- {min,max}
          else
            throw (.invalidRepetition min max)
    )

def concat : All (Imp (Box (SimpleParser Error Ast)) (SimpleParser Error Ast))
  | _, regex => Parser.foldl1 .concat (repetition regex)

-- TODO: we want a different version of `chainl1` that allows empty parse for `concat regex` as `ab||c` is a valid regex.
def alternate : All (Imp (Box (SimpleParser Error Ast)) (SimpleParser Error Ast))
  | _, regex => Parser.chainl1 (concat regex) (charOrError '|' |>.map fun _ e₁ e₂ => .alternate e₁ e₂).box

def regex : All (SimpleParser Error Ast)
  | _ => Box.fix fun regex => alternate regex

def parseAux (s : String) : Except Error Ast :=
  match TParser.Parser.parseCompleteOrElse regex s (throw .remainingInput) with
  | .ok ast => .ok ast
  | .error err => .error err
  | .fatal err => .error err

end Regex.Syntax.Parser
