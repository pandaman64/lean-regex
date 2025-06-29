import Regex.Regex

/-!
# Regex - A Formally Verified Regular Expression Engine

This library provides a robust, formally verified implementation of regular expressions for Lean 4.
It implements two distinct matching algorithms (a backtracker and a virtual machine), both with
complete mathematical proofs of their correctness.

## Features

- **Formally Verified**: Both matching algorithms are mathematically proven to correctly implement
  the semantics of regular expressions
- **Real-World Regex Features**: Support for capture groups, character classes, substring matching,
  and more
- **Two Matching Engines**: Choose between a backtracker or virtual machine implementation
- **Simple API**: Clean, easy-to-use interface for common regex operations

## Installation

Add lean-regex to your Lean project by adding the following to your `lakefile.toml`:

```toml
[[require]]
name = "Regex"
git = "https://github.com/pandaman64/lean-regex"
rev = "v4.20.0"
subDir = "regex"
```

or

```lean
require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "v4.20.0" / "regex"
```

to your `lakefile.lean`.

## Basic Usage

```lean
import Regex

-- Create a regex at compile-time using re! syntax
def dateRegexExample := re! r"\d{4}-\d{2}-\d{2}"

-- Find and return matches (and their positions as components of each `Substring`)
def allMatches := dateRegexExample.findAll
  "2025-05-24: Something happened\\n2025-05-26: Another thing happened"

-- #["2025-05-24".toSubstring, "2025-05-26".toSubstring]
#eval allMatches

-- #[{ byteIdx := 0 }, { byteIdx := 32 }]
#eval allMatches.map (·.startPos)

-- Capture groups
def groupRegexExample := re! r"(a+)(b*)"

def captures := groupRegexExample.capture "aaabb"

/-
Returns captured groups: group 0 = whole match, group 1 = "aaa", group 2 = "bb":

some {
  haystack := "aaabb",
  buffer := #[
    some { byteIdx := 0 }, some { byteIdx := 5 },
    some { byteIdx := 0 }, some { byteIdx := 3 },
    some { byteIdx := 3 }, some { byteIdx := 5 }
  ]
}
-/
#eval captures

-- Additional utility methods are available
def utilityRegexExample := re! r"a+"

def haystack := "a1aa2aaa3"

-- some "a"
#eval utilityRegexExample.extract haystack

-- #["a", "aa", "aaa"]
#eval utilityRegexExample.extractAll haystack

-- true
#eval utilityRegexExample.test haystack

-- 3
#eval utilityRegexExample.count haystack

/-
Splits a string using regex matches as breakpoints:

#["", "1", "2", "3"]

Note the empty substring due to the match "a" at the beginning of the input:
"a1aa2aaa3" = "" ++ "a" ++ "1" ++ "aa" ++ "2" ++ "aaa" ++ "3"
-/
#eval utilityRegexExample.split haystack

```

## API Overview

The library provides the following main structures:

- `Regex`: The main structure representing a compiled regular expression
- `Matches`: A structure for iterating through all matches of a regex in a string
- `Captures`: A structure for iterating through all matches with their capture groups
- `CapturedGroups`: A structure representing the capture groups from a single match

Regex operations include:

- `Regex.find`: Find the first match of a regex in a string
- `Regex.findAll`: Find all matches of a regex in a string
- `Regex.extract`: Extract the first match of a regex in a string
- `Regex.extractAll`: Extract all matches of a regex in a string
- `Regex.capture`: Capture the first match with its capture groups
- `Regex.captureAll`: Capture all matches with their capture groups
- `Regex.replace`: Replace the first match with a replacement string
- `Regex.replaceAll`: Replace all matches with a replacement string
- `Regex.test`: Test if a regex matches a string
- `Regex.count`: Count the number of regex matches in a string
- `Regex.split`: Split a string using regex matches as breakpoints

## Creating Regexes

Regexes can be created in two ways:

1. At compile time using the `re!` macro:
   ```lean
   let regex := re! r"pattern"
   ```
   This checks the regex syntax at compile time and reports errors during compilation.

2. At runtime using `Regex.parse` or `Regex.parse!`:
   ```lean
   let regex ← Regex.parse "pattern" -- Returns Except with possible error
   let regex := Regex.parse! "pattern" -- Panics on invalid syntax
   ```

## Matching Engines

The library provides two matching engines:

1. Virtual Machine (default): Efficient for most regular expressions
2. Backtracker: Can be enabled with `{ regex with useBacktracker := true }`

Both engines are formally verified to be correct implementations of regex semantics.
-/
