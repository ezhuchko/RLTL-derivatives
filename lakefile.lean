import Lake
open Lake DSL

package «regex» {
  -- add any package configuration options here
}

require SymbolicEquivalence from git
  "https://github.com/ezhuchko/symbolic-equivalence.git" @ "main"

@[default_target]
lean_lib «Regex» {
  -- add any library configuration options here
}
