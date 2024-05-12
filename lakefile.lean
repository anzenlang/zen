import Lake
open Lake DSL

package «Zen» where
  -- add package configuration options here

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "main"

@[default_target]
lean_lib «Zen» where
  -- add library configuration options here
