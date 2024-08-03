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

require "leanprover-community" / "mathlib" @ git "v4.10.0"
require "fgdorais" / "Parser" @ git "56d6a480d666c33262a30c87a9e8b74e83805288"

-- TODO: stop using meta if
meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require "leanprover" / "doc-gen4" @ git "32c52a4b35ba8a3d261056e0d264de7bb94c062e"
