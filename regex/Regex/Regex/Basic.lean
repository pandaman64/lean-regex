import Regex.Syntax.Parser
import Regex.NFA
import Regex.VM
import Regex.Backtracker
import Regex.Regex.OptimizationInfo

set_option autoImplicit false

open String (ValidPos Slice)
open Regex.Data (Expr)

/--
A structure representing a compiled regular expression.

This is the main entry point for the regex engine, allowing search and capture operations.
-/
structure Regex where
  nfa : Regex.NFA
  wf : nfa.WellFormed
  maxTag : Nat := nfa.maxTag
  useBacktracker : Bool := false
  optimizationInfo : Regex.OptimizationInfo := default
deriving Repr, DecidableEq

namespace Regex

/--
Captures the next match in the input string with capture groups stored in a fixed-size buffer.

This is a lower-level function that powers the higher-level capture operations.

* `self`: The regex to match against
* `bufferSize`: Size of the buffer to store capture groups
* `p`: Valid position in the input string
* Returns: A buffer containing the matched capture groups, or `none` if no match is found
-/
def captureNextBuf {s : String} (self : Regex) (bufferSize : Nat) (p : ValidPos s) : Option (Buffer s bufferSize) :=
  -- Skip to the next possible starting position
  let start := self.optimizationInfo.findStart p
  if self.useBacktracker then
    Backtracker.captureNextBuf self.nfa self.wf bufferSize start
  else
    VM.captureNextBuf self.nfa self.wf bufferSize start

/--
Searches for the next match in the input string.

* `self`: The regex to match against
* `p`: Valid position in the input string
* Returns: A slice representing the match, or `none` if no match is found
-/
def searchNext {s : String} (self : Regex) (p : ValidPos s) : Option Slice := do
  let slots ← captureNextBuf self 2 p
  let startPos ← slots[0]
  let stopPos ← slots[1]
  if h : startPos ≤ stopPos then
    pure ⟨s, startPos, stopPos, h⟩
  else
    .none

/--
Constructs a `Regex` from a regular expression.

* `expr`: The regular expression to compile
* Returns: A compiled `Regex`
-/
def fromExpr (expr : Expr) : Regex :=
  let nfa := Regex.NFA.compile expr
  let optimizationInfo := OptimizationInfo.fromExpr expr
  { nfa := nfa, wf := Regex.NFA.compile_wf, optimizationInfo := optimizationInfo }

/--
Parses a regular expression string into a `Regex` structure.

* `s`: The regular expression string to parse
* Returns: Either a compiled `Regex` or a parsing error
-/
def parse (s : String) : Except Regex.Syntax.Parser.Error Regex := do
  let expr ← Regex.Syntax.Parser.parse s
  return Regex.fromExpr expr

/--
Parses a regular expression string into a `Regex` structure, panicking on parse error.

* `s`: The regular expression string to parse
* Returns: A compiled `Regex`
* Panics: If the regex syntax is invalid
* Note: Use `Regex.parse` instead if you want to handle parse errors
-/
def parse! (s : String) : Regex :=
  Regex.fromExpr (Regex.Syntax.Parser.parse! s)

end Regex
