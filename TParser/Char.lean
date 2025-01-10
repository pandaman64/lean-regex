import TParser.Parser

set_option autoImplicit false

open String (Iterator)
open TParser.Indexed

namespace TParser.Char

@[inline, specialize]
def anyCharOrElse {m} [Pure m] (unexpectedEof : All (App m (Success Char))) : All (Parser m Char) :=
  Parser.mk fun {it} h =>
    if hn : it.hasNext then
      pure ⟨it.curr' hn, it.next' hn, by simp [Iterator.next_remainingBytes_lt, hn]⟩
    else
      unexpectedEof

@[inline, specialize]
def anyChar {m} [Alternative m] : All (Parser m Char) :=
  anyCharOrElse Alternative.failure

def charOrElse {m} [Monad m] (c : Char) (unexpectedEof : All (App m (Success Char))) (invalidChar : All (App m (Success Char))) :
  All (Parser m Char) :=
  anyCharOrElse unexpectedEof |>.guardOrElse (· = c) invalidChar

def char {m} [Monad m] [Alternative m] (c : Char) : All (Parser m Char) :=
  charOrElse c Alternative.failure Alternative.failure

end TParser.Char
