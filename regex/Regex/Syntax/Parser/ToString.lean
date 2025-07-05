import Regex.Syntax.Ast
import Regex.Syntax.Parser.Basic
import Regex.Data.Classes

set_option autoImplicit false

open Regex.Syntax.Parser (Ast)
open Regex.Data (Anchor PerlClass PerlClassKind Class Classes)

namespace Regex.Syntax.Parser -- Because Ast is there

/-
 Helper for left-padding strings with a character
 (Stolen from Mathlib)
-/
@[inline] private def String.leftpad (n : Nat) (c : Char := ' ') (s : String) : String := ⟨List.leftpad n c s.data⟩

@[inline] private def Char.toHexDigits (c : Char) : String := Nat.toDigits 16 c.val.toNat |>.asString

/-- Characters that require escaping in character class context -/
@[inline] private def classSpecialCharacters : String := "\\]-"

/-- Common escape sequences for control characters -/
@[inline] private def escapeControlChar (c : Char) : Option String :=
  match c with
  | '\n' => some "\\n"
  | '\t' => some "\\t"
  | '\r' => some "\\r"
  | '\x07' => some "\\a"
  | '\x0c' => some "\\f"
  | '\x0b' => some "\\v"
  | '\x00' => some "\\0"
  | '\\' => some "\\\\"
  | _ => none

/-- Convert non-printable character to hex escape sequence -/
@[inline] private def hexEscape (c : Char) : String :=
  if c.val ≤ 255 then
    s!"\\x{String.leftpad 2 '0' (Char.toHexDigits c)}"
  else
    s!"\\u{String.leftpad 4 '0' (Char.toHexDigits c)}"

/-- Core character escaping logic -/
@[inline] private def escapeCharCore (inClass : Bool) (c : Char) : String :=
  -- First check for control character escapes
  match escapeControlChar c with
  | some escaped => escaped
  | none =>
    -- Then check for context-specific special characters
    let needsEscape :=
      if inClass then classSpecialCharacters.contains c
      else specialCharacters.contains c

    if needsEscape then
      s!"\\{c}"
    else if c.val < 32 || c.val > 126 then
      hexEscape c
    else
      c.toString

/-- Escape character for general regex context -/
@[inline] private def escapeChar (c : Char) : String := escapeCharCore false c

/-- Escape character for character class context -/
@[inline] private def escapeCharInClass (c : Char) : String := escapeCharCore true c

@[inline] def PerlClass.toString (pc : PerlClass) : String :=
  let base := match pc.kind with
    | .digit => "d"
    | .space => "s"
    | .word => "w"
  if pc.negated then base.toUpper else base

@[inline] def Class.toString (c : Class) : String :=
  match c with
  | .single ch => escapeCharInClass ch
  | .range start _end _ => s!"{escapeCharInClass start}-{escapeCharInClass _end}"
  | .perl pc => s!"\\{PerlClass.toString pc}"

@[inline] def Classes.toString (cs : Classes) : String :=
  let _prefix := if cs.negated then "[^" else "["
  let classes := cs.classes.map Class.toString |>.toList |> String.intercalate ""
  s!"{_prefix}{classes}]"

@[inline] def Anchor.toString (a : Anchor) : String :=
  match a with
  | .start => "^"
  | .eos => "$"
  | .wordBoundary => "\\b"
  | .nonWordBoundary => "\\B"

-- TODO: consider the precedence of the operators.
def Ast.toString : Ast → String
  | .empty => ""
  | .epsilon => ""
  | .anchor a => Anchor.toString a
  | .char c => escapeChar c
  | .group ast => s!"({ast.toString})"
  | .alternate ast1 ast2 => s!"{ast1.toString}|{ast2.toString}"
  | .concat ast1 ast2 => s!"{ast1.toString}{ast2.toString}"
  | .repeat 0 .none ast => s!"{ast.toString}*"
  | .repeat 1 .none ast => s!"{ast.toString}+"
  | .repeat 0 (.some 1) ast => s!"{ast.toString}?"
  | .repeat min (.some max) ast =>
    if min == max then ast.toString ++ "{" ++ Nat.repr min ++ "}"
    else ast.toString ++ "{" ++ Nat.repr min ++ "," ++ Nat.repr max ++ "}"
  | .repeat min .none ast => ast.toString ++ "{" ++ Nat.repr min ++ ",}"
  | .classes cs => Classes.toString cs
  | .perl pc => s!"\\{PerlClass.toString pc}"
  | .dot => "."

end Regex.Syntax.Parser
