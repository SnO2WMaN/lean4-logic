import Lake
open Lake DSL

package «logic» {
  -- add package configuration options here
}

lean_lib «Logic» {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "25e6049"


@[default_target]
lean_exe «logic» {
  root := `Main
}
