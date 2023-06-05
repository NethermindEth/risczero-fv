import Lake
open Lake DSL

package risc0 {
  -- add package configuration options here
}

lean_lib Risc0 {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "c59c263ccfa439765d0e990b91ab9f4e09541375"

@[default_target]
lean_exe risc0 {
  root := `Main
}
