import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart11

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part12 on st
def part12_state (st: State) : State := 
  
        ((((st["%48"] ←ₛ getImpl st { name := "data" } 0 15)[felts][{ name := "%49" }] ←
              Option.get! (State.felts (st["%48"] ←ₛ getImpl st { name := "data" } 0 15) { name := "%48" }) *
                Option.get! (State.felts st { name := "%4" }))[felts][{ name := "%50" }] ←
            Option.get! (State.felts (st["%48"] ←ₛ getImpl st { name := "data" } 0 15) { name := "%48" }) *
                Option.get! (State.felts st { name := "%4" }) +
              Option.get! (State.felts st { name := "%47" }))[felts][{ name := "%51" }] ←
          (Option.get! (State.felts (st["%48"] ←ₛ getImpl st { name := "data" } 0 15) { name := "%48" }) *
                Option.get! (State.felts st { name := "%4" }) +
              Option.get! (State.felts st { name := "%47" })) *
            Option.get! (State.felts st { name := "%1" })) 

-- Run the whole program by using part12_state rather than Code.part12
def part12_state_update (st: State): State :=
  Γ (part12_state st) ⟦Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part12_state for Code.part12 produces the same result
lemma part12_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part12_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part12
  MLIR
  unfold part12_state_update part12_state
  rewrite [←eq]
  rfl

lemma part12_updates_opaque {st : State} : 
  Code.getReturn (part11_state_update st) ↔
  Code.getReturn (part12_state_update (part11_state st)) := by
  simp [part11_state_update, part12_wp]

end Risc0.ComputeDecode.Constraints.WP