import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₃ on st
def part₃_state (st: State) : State := sorry

-- Run the program from part₃ onwards by using part₃_state rather than Witness.part₃
def part₃_state_update (st: State): State :=
  Γ (part₃_state st) ⟦Witness.part₄; Witness.part₅; Witness.part₆⟧

-- ****************************** WEAKEST PRE - Part₃ ******************************
lemma part₃_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆) st).lastOutput = [y₁, y₂, y₃] ↔
  State.lastOutput (part₃_state_update st) = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₄; Witness.part₅; Witness.part₆) = prog
  unfold Witness.part₃
  MLIR
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************


-- Prove that substituting part₃_state for Witness.part₃ produces the same result
lemma part₃_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₃_state_update st).lastOutput = [y₁, y₂, y₃] := by
  simp only [part₃_state, part₃_state_update, MLIR.runProgram]
  unfold Witness.part₃
  MLIR
  rfl

end Witness

end Risc0.OneHot.WP