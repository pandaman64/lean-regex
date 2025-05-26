# lean-regex

A formally verified regular expression engine for the Lean programming language.

## Overview

lean-regex provides a robust, formally verified implementation of regular expressions for Lean 4. The library implements two distinct matching algorithms (a backtracker and a virtual machine), both with complete mathematical proofs of their correctness.

### Key Features

- **Formally Verified**: Both matching algorithms (backtracker and VM) are mathematically proven to correctly implement the semantics of regular expressions
- **Real-World Regex Features**: Support for capture groups, character classes, substring matching, and more
- **Two Matching Engines**: Choose between a backtracker or virtual machine implementation, both provably correct
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

or

```lean
require Regex from git "https://github.com/pandaman64/lean-regex.git" @ "v4.19.0" / "regex"
```

to your `lakefile.lean`

## Usage

```lean
import Regex

-- Create a regex at compile-time using re! syntax
let regex := re! r"\d{4}-\d{2}-\d{2}"

-- Find matches
let allMatches := regex.findAll "2025-05-24: Something happened\\n2025-05-26: Another thing happened"
-- Returns positions of matches

-- Capture groups
let groupRegex := re! r"(a+)(b*)"
let captures := groupRegex.capture "aaabb"
-- Returns captured groups: group 0 = whole match, group 1 = "aaa", group 2 = "bb"
```

For more details, please check [the API reference](https://pandaman64.github.io/lean-regex/Regex.html).

## Formal Verification

The library's correctness is formally verified through mathematical proofs in Lean 4. This ensures that:

1. **Soundness**: When the engine reports a match, it correctly follows the formal semantics of regular expressions
2. **Completeness**: When the engine reports no match, there truly is no match according to the formal semantics
3. **Capture Correctness**: Capture groups correctly identify the matched substrings

## Contributing

Contributions are welcome! Please start by creating an issue to discuss your proposed changes before submitting a Pull Request.

## License

This project is licensed under the Apache License 2.0.

