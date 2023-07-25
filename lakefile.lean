import Lake
open Lake DSL

def globalArgs := #[
  "-Dlinter.deprecated=false",
  "-Dlinter.suspiciousUnexpanderPatterns=false",
  "-Dlinter.unusedVariables=false",
  "-DwarningAsError=true"
]

package risc0 {
  moreLeanArgs := globalArgs
  moreServerArgs := globalArgs
}

lean_lib Risc0 {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "ab4ba6c49d41daca175dc9bbeb5f493ece93c2f6"

@[default_target]
lean_exe risc0 {
  root := `Main
}
