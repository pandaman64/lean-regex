import Lake
open Lake DSL

package Regex where
  -- add package configuration options here

lean_lib Regex where
  -- add library configuration options here

lean_lib RegexCorrectness where
  -- add library configuration options here

-- TODO: make a proper test_driver
lean_exe Test where

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.8.0"

require Parser from git
  "https://github.com/fgdorais/lean4-parser" @ "3d98183d1446d27c831e911be1f428f2b0466eb6"

-- TODO: stop using meta if
meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "c7f4ac84b973b6efd8f24ba2b006cad1b32c9c53"
