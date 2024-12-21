import Batteries.Data.String

set_option autoImplicit false

namespace Regex.Data

structure Span where
  l : List Char
  m : List Char
  r : List Char

def Span.curr (s : Span) : String.Pos := ⟨String.utf8Len s.l + String.utf8Len s.m⟩

end Regex.Data
