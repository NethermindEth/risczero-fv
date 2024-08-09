import Lake
open Lake DSL

def globalArgs := #[
  "-Dlinter.deprecated=false",
  "-Dlinter.suspiciousUnexpanderPatterns=false",
  "-Dlinter.unusedVariables=false",
  "-DwarningAsError=true",
  "-Dpp.deepTerms=true",
  "-Dpp.maxSteps=20000",
  "-Dlinter.haveLet=0"
]

package risc0 {
  moreLeanArgs := globalArgs
  moreServerOptions := #[
    ⟨`Dlinter.deprecated, false⟩,
    ⟨`Dlinter.suspiciousUnexpanderPatterns, false⟩,
    ⟨`Dlinter.unusedVariables, false⟩,
    ⟨`Dlinter.DwarningAsError, true⟩,
    ⟨`Dpp.deepTerms, true⟩,
    ⟨`Dpp.maxSteps, .ofNat 20000⟩,
    ⟨`Dlinter.haveLet, .ofNat 0⟩
  ]
}

lean_lib Risc0 {
  -- add library configuration options here
}

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git"@"e2938e094a7a98a6f18f06ac1bd15cc0d2e89c8e"

@[default_target]
lean_exe risc0 {
  root := `Main
}
