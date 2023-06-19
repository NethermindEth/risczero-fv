import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₀ on st
def part₀_state (st: State) : State :=
  ((((st[felts][{ name := "1" }] ← 1)[felts][{ name := "2" }] ← 2)[props][{ name := "true" }] ← True)["input"] ←ₛ
        getImpl st { name := "input" } 0 0)

-- Run the whole program by using part₀_state rather than Code.part₀
def part₀_state_update (st: State): State :=
  Γ (part₀_state st) ⟦Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₀_state for Code.part₀ produces the same result
lemma part₀_wp {st : State} :
  Code.run st ↔
  Code.getReturn (part₀_state_update st) := by
  unfold Code.run MLIR.runProgram; simp only
  rewrite [Code.parts_combine]; unfold Code.parts_combined
  generalize eq : (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl

end Risc0.OneHot.Constraints.WP
