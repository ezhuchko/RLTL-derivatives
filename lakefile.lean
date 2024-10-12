import Lake
open Lake DSL

package «regex» {
  -- add any package configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_lib «Regex» {
  -- add any library configuration options here
}
