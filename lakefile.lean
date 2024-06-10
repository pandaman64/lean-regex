import Lake
open Lake DSL

package Regex where
  -- add package configuration options here

lean_lib Regex where
  -- add library configuration options here

lean_lib RegexCorrectness where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

require Parser from git
  "https://github.com/fgdorais/lean4-parser" @ "3d98183d1446d27c831e911be1f428f2b0466eb6"
