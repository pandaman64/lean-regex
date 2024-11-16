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

require "leanprover-community" / "mathlib" @ git "v4.13.0"
require "fgdorais" / "Parser" @ git "176dab14ce044b48203d159ef604e04d7e050fa2"

-- TODO: stop using meta if
meta if get_config? doc = some "on" then -- do not download and build doc-gen4 by default
require "leanprover" / "doc-gen4" @ git "v4.13.0"
