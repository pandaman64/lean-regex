import TParser
import Regex.Syntax.Ast

set_option autoImplicit false

open TParser (SimpleParser Parser)
open TParser.Indexed
open TParser.Char
open Regex.Data (PerlClass PerlClassKind Class Expr)

namespace Regex.Syntax.Parser

inductive Error where
  | unexpectedEof
  | unexpectedChar
  | unexpectedEscapedChar (c : Char)
  | unexpectedPerlClass (cls : PerlClass)
  | invalidHexDigit (c : Char)
  | remainingInput
deriving Repr

def specialCharacters := "[](){}*+?|^$.\\"

def charOrElse' (c : Char) : All (SimpleParser Error Char) :=
  charOrElse c (throw .unexpectedEof) (throw .unexpectedChar)

def hexDigit : All (SimpleParser Error Nat) :=
  anyCharOrElse (throw .unexpectedEof)
  |>.andBindM fun c =>
    if c.isDigit then pure (c.toNat - '0'.toNat)
    else if 'a' ≤ c && c ≤ 'f' then pure (c.toNat - 'a'.toNat + 10)
    else if 'A' ≤ c && c ≤ 'F' then pure (c.toNat - 'A'.toNat + 10)
    else throw (.invalidHexDigit c)

-- TODO: commit after '\\'?
def escapedChar : All (SimpleParser Error (Char ⊕ PerlClass)) :=
  charOrElse' '\\'
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
    charOrElse' 'x'
    |>.andBindR fun _ => Parser.box $
      hexDigit.and hexDigit.box
      |>.map fun (d₁, d₂) => Char.ofNat (16 * d₁ + d₂)
  hexU : All (SimpleParser Error Char) :=
    charOrElse' 'u'
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

def escapedCharWithoutPerlClasses : All (SimpleParser Error Char) :=
  escapedChar
  |>.andBindM fun
    | .inl c => pure c
    | .inr cls => throw (.unexpectedPerlClass cls)

def plainChar : All (SimpleParser Error Char) :=
  anyCharOrElse (throw .unexpectedEof)
  |>.andBindM fun c =>
    if specialCharacters.contains c then throw (.unexpectedEscapedChar c)
    else pure c

end Regex.Syntax.Parser
