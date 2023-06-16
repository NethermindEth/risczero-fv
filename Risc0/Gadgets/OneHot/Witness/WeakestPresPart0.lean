import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₀ on st
def part₀_state (st: State) : State :=
  (State.updateFelts
    (State.updateFelts
      (State.updateFelts st
        { name := "2" } 2)
        { name := "1" } 1)
        { name := "0" } 0)["input"] ←ₛ getImpl st { name := "input" } 0 0

-- Run the whole program by using part₀_state rather than Witness.part₀
def part₀_state_update (st: State): State :=
  Γ (part₀_state st) ⟦Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈⟧

-- ****************************** WEAKEST PRE - Part₀ ******************************
lemma part₀_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  Witness.run st = [y₁, y₂, y₃] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold Witness.run MLIR.runProgram; simp only
  rewrite [Witness.parts_combine]; unfold Witness.parts_combined
  generalize eq : (Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈) = prog
  unfold Witness.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₀ ******************************

-- REVIEW: This is basically the same as part₀_wp?
-- Prove that substituting part₀_state for Witness.part₀ produces the same result
lemma part₀_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₀; Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈) = prog
  unfold Witness.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl

end Witness

end Risc0.OneHot.WP