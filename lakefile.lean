import Lake
open Lake DSL

package zen where
  -- add package configuration options here

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "v4.10.0"

@[default_target]
lean_lib «Zen» where
  -- add library configuration options here
