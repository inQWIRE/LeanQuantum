import Lake
open Lake DSL

package «quantumlib» where
  -- add package configuration options here

@[default_target]
lean_lib «Quantumlib» where
  -- add library configuration options here

require mathlib from git
  "https://github.com/leanprover-community/mathlib4"
