import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₀ on st
def part₀_state (st: State) : State :=
  (State.updateFelts
    (State.updateFelts
      (State.updateFelts st
        { name := "2" } 2)
        { name := "1" } 1)
        { name := "0" } 0)["input"] ←ₛ getImpl st { name := "input" } 0 0

-- Run the whole program by using part₀_state rather than Code.part₀
def part₀_state_update (st: State): State :=
  Γ (part₀_state st) ⟦Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₀_state for Code.part₀ produces the same result
-- ****************************** WEAKEST PRE - Part₀ ******************************
lemma part₀_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  Code.run st = [y₁, y₂, y₃] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold Code.run MLIR.runProgram; simp only
  rewrite [Code.parts_combine]; unfold Code.parts_combined
  generalize eq : (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₀ ******************************

end Risc0.OneHot.Witness.WP
