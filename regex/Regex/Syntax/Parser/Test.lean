-- Unit tests for the regex parser.
import Regex.Syntax.Parser.Basic

namespace Regex.Syntax.Parser.Test

private def decEq (a b : Except Error Ast) : Decidable (a = b) :=
  match a, b with
  | .ok a, .ok b =>
    if eq : a = b then
      isTrue (congrArg _ eq)
    else
      isFalse (by simp_all)
  | .error a, .error b =>
    if eq : a = b then
      isTrue (congrArg _ eq)
    else
      isFalse (by simp_all)
  | .ok _, .error _ => isFalse (by simp_all)
  | .error _, .ok _ => isFalse (by simp_all)

local instance : DecidableEq (Except Error Ast) := decEq

-- Helper function to test roundtrip: parse -> toString -> parse should equal original
private def test (input : String) (expected : Ast) : Bool :=
  match parseAst input with
  | .ok ast => ast = expected
  | .error _ => false

#guard test "(a)" (.group (.char 'a'))
#guard test "(?:a)" (.char 'a')

#guard test "^" (.anchor .start)
#guard test "$" (.anchor .eos)
#guard test "^abc$" (.concat (.concat (.concat (.concat (.anchor .start) (.char 'a')) (.char 'b')) (.char 'c')) (.anchor .eos))

#guard test "[abc]" (.classes ⟨false, #[.single 'a', .single 'b', .single 'c']⟩)
#guard test "[^abc]" (.classes ⟨true, #[.single 'a', .single 'b', .single 'c']⟩)
#guard test "[a-z]" (.classes ⟨false, #[.range 'a' 'z']⟩)
#guard test r"[\da]" (.classes ⟨false, #[.perl ⟨false, .digit⟩, .single 'a']⟩)
#guard test "[-]" (.classes ⟨false, #[.single '-']⟩)
#guard test "[a-]" (.classes ⟨false, #[.single 'a', .single '-']⟩)
-- special characters are allowed in classes
#guard test r"[(){}*+?|^$.\--]" (.classes ⟨false, #[
  '(', ')', '{', '}', '*', '+', '?', '|', '^', '$', '.', '-', '-'
].map .single⟩)

#guard test "|" (.alternate .epsilon .epsilon)
#guard test "a|" (.alternate (.char 'a') .epsilon)
#guard test "|a" (.alternate .epsilon (.char 'a'))
#guard test "a|b" (.alternate (.char 'a') (.char 'b'))
#guard test "a|b|c" (.alternate (.alternate (.char 'a') (.char 'b')) (.char 'c'))
#guard test "ab|cd(e|f)" (.alternate
  (.concat (.char 'a') (.char 'b'))
  (.concat (.concat (.char 'c') (.char 'd')) (.group (.alternate (.char 'e') (.char 'f')))))

#guard test "a*b*c*" (.concat (.concat (.repeat 0 none true (.char 'a')) (.repeat 0 none true (.char 'b'))) (.repeat 0 none true (.char 'c')))
#guard test "a?" (.repeat 0 (some 1) true (.char 'a'))
#guard test "a*?" (.repeat 0 none false (.char 'a'))
#guard test "a+?" (.repeat 1 none false (.char 'a'))
#guard test "a*??" (.repeat 0 (some 1) true (.repeat 0 none false (.char 'a')))
#guard test "a+??" (.repeat 0 (some 1) true (.repeat 1 none false (.char 'a')))
#guard test "a{1,2}" (.repeat 1 (some 2) true (.char 'a'))
#guard test "a{1,2}?" (.repeat 1 (some 2) false (.char 'a'))
#guard test "a{2}" (.repeat 2 (some 2) true (.char 'a'))
#guard test "a{2}?" (.repeat 2 (some 2) false (.char 'a'))
#guard test "a{2,}?" (.repeat 2 none false (.char 'a'))
#guard test "a{2,}?" (.repeat 2 none false (.char 'a'))

-- escaping rules for special characters
#guard test "\\n" (.char '\n')
#guard test "\\t" (.char '\t')
#guard test "\\r" (.char '\r')
#guard test "\\a" (.char '\x07')
#guard test "\\f" (.char '\x0c')
#guard test "\\v" (.char '\x0b')
#guard test "\\0" (.char '\x00')
#guard test "\\-" (.char '-')
#guard test "\\[" (.char '[')
#guard test "\\]" (.char ']')
#guard test "\\(" (.char '(')
#guard test "\\)" (.char ')')
#guard test "\\{" (.char '{')
#guard test "\\}" (.char '}')
#guard test "\\*" (.char '*')
#guard test "\\+" (.char '+')
#guard test "\\?" (.char '?')
#guard test "\\|" (.char '|')
#guard test "\\^" (.char '^')
#guard test "\\$" (.char '$')
#guard test "\\." (.char '.')
#guard test "\\\\" (.char '\\')

#guard test "\\xab" (.char '\xab')
#guard test "\\u1234" (.char '\u1234')

#guard test "\\d" (.perl ⟨false, .digit⟩)
#guard test "\\D" (.perl ⟨true, .digit⟩)
#guard test "\\s" (.perl ⟨false, .space⟩)
#guard test "\\S" (.perl ⟨true, .space⟩)
#guard test "\\w" (.perl ⟨false, .word⟩)
#guard test "\\W" (.perl ⟨true, .word⟩)

#guard parseAst "\\z" = .error (.unexpectedEscapedChar 'z')
#guard parseAst "\\g" = .error (.unexpectedEscapedChar 'g')

-- '}' is not a special character
#guard test "}" (.char '}')

-- syntax errors and error messages
#guard parseAst "a{1,|bx" = .error (.unexpectedChar '|')
#guard parseAst "(" = .error .unexpectedEof
#guard parseAst ")" = .error .expectedEof
#guard parseAst "(abc" = .error .unexpectedEof
#guard parseAst "abc)" = .error .expectedEof
#guard parseAst "[abc" = .error .unexpectedEof
#guard parseAst "abc]" = .error .expectedEof
#guard parseAst "a{}" = .error (.unexpectedChar '}')
#guard parseAst "a{,}" = .error (.unexpectedChar ',')
#guard parseAst "a{,5}" = .error (.unexpectedChar ',')
#guard parseAst "a{-1}" = .error (.unexpectedChar '-')
#guard parseAst "a{-1,5}" = .error (.unexpectedChar '-')
#guard parseAst "a{10,5}" = .error .(.invalidRepetition 10 5)
#guard parseAst "*a" = .error .expectedEof
#guard parseAst "+a" = .error .expectedEof
#guard parseAst "?a" = .error .expectedEof
#guard parseAst "|*" = .error .expectedEof
#guard parseAst "\\x" = .error .unexpectedEof
#guard parseAst "\\u" = .error .unexpectedEof
#guard parseAst "\\u12" = .error .unexpectedEof
#guard parseAst "[]" = .error (.unexpectedChar ']')
#guard parseAst "[^]" = .error (.unexpectedChar ']')
#guard parseAst "a{1" = .error .unexpectedEof
#guard parseAst "a{1," = .error .unexpectedEof
#guard parseAst "a{1,2" = .error .unexpectedEof
#guard parseAst "a{," = .error (.unexpectedChar ',')
#guard parseAst "a)" = .error .expectedEof
#guard parseAst "(?:" = .error .unexpectedEof
#guard parseAst "(?:a" = .error .unexpectedEof
#guard parseAst "(?:" = .error .unexpectedEof

-- Minimum
#guard parseAst "\\u{0}" = .ok (.char '\x00')

-- ASCII range
#guard parseAst "\\u{7F}" = .ok (.char '\x7F')
#guard parseAst "\\u{41}" = .ok (.char 'A')

-- Latin-1 Supplement
#guard parseAst "\\u{80}" = .ok (.char (Char.ofNat 0x80))
#guard parseAst "\\u{FF}" = .ok (.char 'ÿ')

-- BMP (Basic Multilingual Plane)
#guard parseAst "\\u{1234}" = .ok (.char (Char.ofNat 0x1234))
#guard parseAst "\\u{FFFF}" = .ok (.char (Char.ofNat 0xFFFF))

-- Supplementary planes (emoji and beyond)
#guard parseAst "\\u{10000}" = .ok (.char (Char.ofNat 0x10000))
#guard parseAst "\\u{1F600}" = .ok (.char '😀')  -- GRINNING FACE
#guard parseAst "\\u{1F4A9}" = .ok (.char '💩')  -- PILE OF POO
#guard parseAst "\\u{1F47D}" = .ok (.char '👽')  -- EXTRATERRESTRIAL ALIEN

-- Maximum valid code point
#guard parseAst "\\u{10FFFF}" = .ok (.char (Char.ofNat 0x10FFFF))

-- Lowercase hex digits
#guard parseAst "\\u{1f600}" = .ok (.char '😀')
#guard parseAst "\\u{abcd}" = .ok (.char (Char.ofNat 0xABCD))

-- Variable length (1-6 digits)
#guard parseAst "\\u{a}" = .ok (.char (Char.ofNat 0xA))
#guard parseAst "\\u{AB}" = .ok (.char (Char.ofNat 0xAB))
#guard parseAst "\\u{ABC}" = .ok (.char (Char.ofNat 0xABC))
#guard parseAst "\\u{ABCD}" = .ok (.char (Char.ofNat 0xABCD))
#guard parseAst "\\u{ABCDE}" = .ok (.char (Char.ofNat 0xABCDE))

-- Empty braces
#guard parseAst "\\u{}" = .error (.unexpectedChar '}')

-- Too large (beyond Unicode)
#guard parseAst "\\u{110000}" = .error (.invalidCodePoint 0x110000)
#guard parseAst "\\u{FFFFFF}" = .error (.invalidCodePoint 0xFFFFFF)

-- Too many digits (>6)
#guard parseAst "\\u{1234567}" = .error (.tooManyHexDigits 7)

-- Invalid hex characters
#guard parseAst "\\u{GHIJ}" = .error (.invalidHexChar 'G')
#eval parseAst "\\u{12.34}"
#guard parseAst "\\u{12.34}" = .error (.invalidHexChar '.')

-- Missing closing brace
#guard parseAst "\\u{1234" = .error (.unexpectedEndOfInput)

-- Surrogate range (optional, depending on Lean's Char behavior)
-- If Lean's Char.ofNat rejects surrogates, these should error:
#guard parseAst "\\u{D800}" = .error (.invalidCodePoint 0xD800)
#guard parseAst "\\u{DFFF}" = .error (.invalidCodePoint 0xDFFF)

end Regex.Syntax.Parser.Test
