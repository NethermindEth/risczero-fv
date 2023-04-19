import Lake
open Lake DSL

package is0 {
  -- add package configuration options here
}

lean_lib Is0 {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"

@[default_target]
lean_exe is0 {
  root := `Main
}
