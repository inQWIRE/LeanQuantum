import Lake
open Lake DSL

package «quantumlib» where
  -- add package configuration options here

lean_lib «Quantumlib» where
  -- add library configuration options here

@[default_target]
lean_exe «quantumlib» where
  root := `Main

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
