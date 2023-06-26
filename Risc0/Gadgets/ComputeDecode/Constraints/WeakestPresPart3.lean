import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart2

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part3 on st
def part3_state (st: State) : State := 
  
        ((((st["%12"] ←ₛ getImpl st { name := "data" } 0 0)["%13"] ←ₛ
              getImpl st { name := "data" } 0 8)[felts][{ name := "%14" }] ←
            Option.get! (State.felts (st["%13"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%13" }) *
              Option.get! (State.felts st { name := "%4" }))["%15"] ←ₛ
          getImpl st { name := "data" } 0
            9) 

-- Run the whole program by using part3_state rather than Code.part3
def part3_state_update (st: State): State :=
  Γ (part3_state st) ⟦Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part3_state for Code.part3 produces the same result
lemma part3_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part3; Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part3_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part3
  MLIR
  unfold part3_state_update part3_state
  rewrite [←eq]
  rfl

lemma part3_updates_opaque {st : State} : 
  Code.getReturn (part2_state_update st) ↔
  Code.getReturn (part3_state_update (part2_state st)) := by
  simp [part2_state_update, part3_wp]

end Risc0.ComputeDecode.Constraints.WP