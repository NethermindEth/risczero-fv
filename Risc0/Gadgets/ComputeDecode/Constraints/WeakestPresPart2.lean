import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart1

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part2 on st
def part2_state (st: State) : State := 
  
        ((((st["%8"] ←ₛ getImpl st { name := "in" } 0 1)["%9"] ←ₛ getImpl st { name := "in" } 0 2)["%10"] ←ₛ
            getImpl st { name := "in" } 0 3)["%11"] ←ₛ
          getImpl st { name := "data" } 0
            13) 

-- Run the whole program by using part2_state rather than Code.part2
def part2_state_update (st: State): State :=
  Γ (part2_state st) ⟦Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part2_state for Code.part2 produces the same result
lemma part2_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part2; Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part2_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part2
  MLIR
  unfold part2_state_update part2_state
  rewrite [←eq]
  rfl

lemma part2_updates_opaque {st : State} : 
  Code.getReturn (part1_state_update st) ↔
  Code.getReturn (part2_state_update (part1_state st)) := by
  simp [part1_state_update, part2_wp]

end Risc0.ComputeDecode.Constraints.WP