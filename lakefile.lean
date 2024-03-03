import Lake
open Lake DSL

package Regex where
  -- add package configuration options here

lean_lib Regex where
  -- add library configuration options here

lean_lib RegexCorrectness where
  -- add library configuration options here

lean_exe RunRegex where
  root := `RunRegex

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.6.0"

require Parser from git
  "https://github.com/fgdorais/lean4-parser" @ "main"
