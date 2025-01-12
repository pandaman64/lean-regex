import Regex.Data.Classes

set_option autoImplicit false

open Regex.Data (PerlClass)

namespace Regex.Syntax.Parser

inductive Error where
  | unexpectedEof
  | unexpectedChar (c : Char)
  | unexpectedEscapedChar (c : Char)
  | unexpectedPerlClassInRange (cls : PerlClass)
  | invalidRange (c₁ : Char) (c₂ : Char)
  | invalidRepetition (min : Nat) (max : Nat)
  | expectedEof
deriving Repr, Inhabited

instance : ToString Error where
  toString := fun e =>
    match e with
    | .unexpectedEof => "unexpected EOF"
    | .unexpectedChar c => s!"unexpected character: {c}"
    | .unexpectedEscapedChar c => s!"unexpected escaped character: {c}"
    | .unexpectedPerlClassInRange cls => s!"unexpected Perl class in range: {reprStr cls}"
    | .invalidRange c₁ c₂ => s!"invalid range: {c₁}..{c₂}"
    | .invalidRepetition min max => s!"invalid repetition: {min}..{max}"
    | .expectedEof => "expected EOF"

end Regex.Syntax.Parser
