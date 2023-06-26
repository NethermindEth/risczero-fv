import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part0 on st
def part0_state (st : State) : State :=
  
        ((((st[felts][{ name := "%0" }] ← 128)[felts][{ name := "%1" }] ← 16)[felts][{ name := "%2" }] ←
            8)[felts][{ name := "%3" }] ←
          2) 

-- Run the whole program by using part0_state rather than Code.part0
def part0_state_update (st : State) : State :=
  Γ (part0_state st) ⟦Code.part1; Code.part2; Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part0_state for Code.part0 produces the same result
lemma part0_wp {st : State} :
  Code.run st ↔
  Code.getReturn (part0_state_update st) := by
    unfold Code.run MLIR.runProgram; simp only
    rewrite [←Code.parts_combine]; unfold Code.parts_combined
    generalize eq : (Code.part1; Code.part2; Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
    unfold Code.part0
    MLIR
    unfold part0_state_update part0_state
    rw [←eq]

end Risc0.ComputeDecode.Constraints.WP