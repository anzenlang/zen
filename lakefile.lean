import Lake
open Lake DSL

package zen where
  -- add package configuration options here

require batteries from
  git "https://github.com/leanprover-community/batteries" @ "v4.15.0"

lean_lib «Zen» where
  -- add library configuration options here

@[default_target]
lean_exe zen where
  root := `Main
