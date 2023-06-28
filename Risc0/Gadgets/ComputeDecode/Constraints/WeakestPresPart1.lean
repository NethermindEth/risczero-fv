import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart0

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part1 on st
def part1_state (st: State) : State := 
  
        ((((st[felts][{ name := "%4" }] ← 4)[felts][{ name := "%5" }] ← 64)[props][{ name := "%6" }] ← True)["%7"] ←ₛ
          getImpl st { name := "in" } 0
            0) 

-- Run the whole program by using part1_state rather than Code.part1
def part1_state_update (st: State): State :=
  Γ (part1_state st) ⟦Code.part2; Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part1_state for Code.part1 produces the same result
lemma part1_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part1; Code.part2; Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part1_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part2; Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part1
  MLIR
  unfold part1_state_update part1_state
  rewrite [←eq]
  rfl

lemma part1_updates_opaque {st : State} : 
  Code.getReturn (part0_state_update st) ↔
  Code.getReturn (part1_state_update (part0_state st)) := by
  simp [part0_state_update, part1_wp]

end Risc0.ComputeDecode.Constraints.WP