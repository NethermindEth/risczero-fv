import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.Code

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₀ on st
def part₀_state (st : State) : State :=
  let one := 0
  let zero := 1
  let true_ := 2
  ((st[one] ←ₛ some (Lit.Val 1))[zero] ←ₛ some (Lit.Val 0))[true_] ←ₛ some (Lit.Constraint True)

-- Run the whole program by using part₀_state rather than Code.part₀
def part₀_state_update (st : State) : State :=
  Γ (part₀_state st) ⟦Code.part₁; Code.part₂; Code.part₃; Code.part₄⟧

-- Prove that substituting part₀_state for Code.part₀ produces the same result
lemma part₀_wp {st : State} :
  Code.run st ↔
  Code.getReturn (part₀_state_update st) := by
  unfold Code.run MLIR.runProgram; simp only
  rewrite [Code.parts_combine]; unfold Code.parts_combined
  generalize eq : (Code.part₁; Code.part₂; Code.part₃; Code.part₄) = prog
  unfold Code.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl

end Risc0.IsZero.Constraints.WP
