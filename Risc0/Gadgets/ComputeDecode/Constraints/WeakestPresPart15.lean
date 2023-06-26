import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart14

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part15 on st
def part15_state (st: State) : State := 
  
        ((((st["%60"] ←ₛ getImpl st { name := "data" } 0 16)[felts][{ name := "%61" }] ←
              Option.get! (State.felts (st["%60"] ←ₛ getImpl st { name := "data" } 0 16) { name := "%60" }) *
                Option.get! (State.felts st { name := "%0" }))[felts][{ name := "%62" }] ←
            Option.get! (State.felts (st["%60"] ←ₛ getImpl st { name := "data" } 0 16) { name := "%60" }) *
                Option.get! (State.felts st { name := "%0" }) +
              Option.get! (State.felts st { name := "%59" }))[felts][{ name := "%63" }] ←
          Option.get! (State.felts st { name := "%7" }) -
            (Option.get! (State.felts (st["%60"] ←ₛ getImpl st { name := "data" } 0 16) { name := "%60" }) *
                Option.get! (State.felts st { name := "%0" }) +
              Option.get! (State.felts st { name := "%59" }))) 

-- Run the whole program by using part15_state rather than Code.part15
def part15_state_update (st: State): State :=
  Γ (part15_state st) ⟦Code.part16⟧

-- Prove that substituting part15_state for Code.part15 produces the same result
lemma part15_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part15; Code.part16) st) ↔
  Code.getReturn (part15_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part16) = prog
  unfold Code.part15
  MLIR
  unfold part15_state_update part15_state
  rewrite [←eq]
  rfl

lemma part15_updates_opaque {st : State} : 
  Code.getReturn (part14_state_update st) ↔
  Code.getReturn (part15_state_update (part14_state st)) := by
  simp [part14_state_update, part15_wp]

end Risc0.ComputeDecode.Constraints.WP