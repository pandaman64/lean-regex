import Regex.Syntax.Parser
import Regex.NFA
import Regex.VM
import Regex.Backtracker

set_option autoImplicit false

open String (Iterator)

/-- 
A structure representing a compiled regular expression.

This is the main entry point for the regex engine, allowing search and capture operations.
-/
structure Regex where
  nfa : Regex.NFA
  wf : nfa.WellFormed
  maxTag : Nat := nfa.maxTag
  useBacktracker : Bool := false
deriving Repr

namespace Regex

/-- 
Captures the next match in the input string with capture groups stored in a fixed-size buffer.

This is a lower-level function that powers the higher-level capture operations.

* `self`: The regex to match against
* `bufferSize`: Size of the buffer to store capture groups
* `it`: String iterator pointing to the current position in the input string
* Returns: An optional buffer containing the matched capture groups, or `none` if no match is found
-/
def captureNextBuf (self : Regex) (bufferSize : Nat) (it : Iterator) : Option (Buffer bufferSize) :=
  if self.useBacktracker then
    Backtracker.captureNextBuf self.nfa self.wf bufferSize it
  else
    VM.captureNextBuf self.nfa self.wf bufferSize it

/--
Searches for the next match in the input string.

* `self`: The regex to match against
* `it`: String iterator pointing to the current position in the input string
* Returns: An optional substring representing the match, or `none` if no match is found
-/
def searchNext (self : Regex) (it : Iterator) : Option Substring :=  do
  let slots ← captureNextBuf self 2 it
  pure ⟨it.toString, ←slots[0], ←slots[1]⟩

/--
Parses a regular expression string into a `Regex` structure.

* `s`: The regular expression string to parse
* Returns: Either a compiled `Regex` or a parsing error
-/
def parse (s : String) : Except Regex.Syntax.Parser.Error Regex := do
  let expr ← Regex.Syntax.Parser.parse s
  let nfa := Regex.NFA.compile expr
  return { nfa := nfa, wf := Regex.NFA.compile_wf }

/--
Parses a regular expression string into a `Regex` structure, raising an exception on parse error.

* `s`: The regular expression string to parse
* Returns: A compiled `Regex`
* Throws: If the regex syntax is invalid
-/
def parse! (s : String) : Regex :=
  let nfa := Regex.NFA.compile (Regex.Syntax.Parser.parse! s)
  { nfa := nfa, wf := Regex.NFA.compile_wf }

end Regex
