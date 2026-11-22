module

public import RegexVibe.VM.Refined

/-!
Flat PikeVM for `Regex`.

This package imports the verified `Regex` library and adds an unboxed engine:
character classes compiled to a Latin-1 bitmap plus a high-run scan, and a
PikeVM whose NFA, ε-stack, and capture slots live in flat `ByteArray`s.
The stock NFA and the stock VM stay the specification. `lake exe Bench --check`
compares the two on the built-in cases.
-/
