import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₀ on st
def part₀_state (st: State) : State :=
  let one := 0
  let x := 1
  (State.updateFelts st { name := one } 1)[x] ←ₛ getImpl st { name := Input } 0 0

-- Run the whole program by using part₀_state rather than Code.part₀
def part₀_state_update (st: State): State :=
  Γ (part₀_state st) ⟦Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅⟧

-- Prove that substituting part₀_state for Code.part₀ produces the same result
lemma part₀_wp {st : State} {y₁ y₂ : Option Felt} :
  Code.run st = [y₁, y₂] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂] := by
  unfold Code.run MLIR.runProgram; simp only
  rewrite [Code.parts_combine]; unfold Code.parts_combined
  generalize eq : (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅) = prog
  unfold Code.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl

end Risc0.IsZero.Witness.WP
