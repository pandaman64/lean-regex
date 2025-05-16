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
rev = "v4.19.0"
subDir = "regex"
```

## Basic Usage

```lean
-- Create a regex at compile-time using re! syntax
let emailRegex := re! r"[a-zA-Z0-9_]+@[a-zA-Z0-9]+\.[a-zA-Z]{2,}"

-- Find matches
let matches := emailRegex.findAll "Contact us at info@example.com or support@company.org"

-- Capture groups
let groupRegex := re! r"(a+)(b*)"
let captures := groupRegex.capture "aaabb"
-- Returns captured groups: group 0 = whole match, group 1 = "aaa", group 2 = "bb"
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
- `Regex.capture`: Capture the first match with its capture groups
- `Regex.captureAll`: Capture all matches with their capture groups
- `Regex.replace`: Replace the first match with a replacement string
- `Regex.replaceAll`: Replace all matches with a replacement string

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
