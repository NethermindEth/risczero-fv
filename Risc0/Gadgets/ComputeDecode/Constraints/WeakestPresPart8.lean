import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart7

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part8 on st
def part8_state (st: State) : State := 
  
        ((((st["%32"] ←ₛ getImpl st { name := "data" } 0 11)["%33"] ←ₛ
              getImpl st { name := "data" } 0 2)[felts][{ name := "%34" }] ←
            Option.get! (State.felts (st["%33"] ←ₛ getImpl st { name := "data" } 0 2) { name := "%33" }) *
              Option.get! (State.felts st { name := "%3" }))["%35"] ←ₛ
          getImpl st { name := "data" } 0
            12) 

-- Run the whole program by using part8_state rather than Code.part8
def part8_state_update (st: State): State :=
  Γ (part8_state st) ⟦Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part8_state for Code.part8 produces the same result
lemma part8_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part8_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part8
  MLIR
  unfold part8_state_update part8_state
  rewrite [←eq]
  rfl

lemma part8_updates_opaque {st : State} : 
  Code.getReturn (part7_state_update st) ↔
  Code.getReturn (part8_state_update (part7_state st)) := by
  simp [part7_state_update, part8_wp]

end Risc0.ComputeDecode.Constraints.WP