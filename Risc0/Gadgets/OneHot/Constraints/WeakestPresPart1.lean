import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart0

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₁ on st
def part₁_state (st: State) : State :=
  (st["output[1]"] ←ₛ getImpl st { name := "output" } 0 1)["output[2]"] ←ₛ
        getImpl st { name := "output" } 0 2

-- Run the whole program by using part₁_state rather than Code.part₁
def part₁_state_update (st: State): State :=
  Γ (part₁_state st) ⟦Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₁_state for Code.part₁ produces the same result
lemma part₁_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₁_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₁
  MLIR
  unfold part₁_state_update part₁_state
  rewrite [←eq]
  rfl

lemma part₁_updates_opaque {st : State} : 
  Code.getReturn (part₀_state_update st) ↔
  Code.getReturn (part₁_state_update (part₀_state st)) := by
  simp [part₀_state_update, part₁_wp]

end Risc0.OneHot.Constraints.WP
