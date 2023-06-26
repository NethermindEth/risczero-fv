import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart8

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part9 on st
def part9_state (st: State) : State := 
  
        ((((st[felts][{ name := "%36" }] ←
                Option.get! (State.felts st { name := "%35" }) *
                  Option.get! (State.felts st { name := "%2" }))[felts][{ name := "%37" }] ←
              Option.get! (State.felts st { name := "%35" }) * Option.get! (State.felts st { name := "%2" }) +
                Option.get! (State.felts st { name := "%34" }))[felts][{ name := "%38" }] ←
            Option.get! (State.felts st { name := "%35" }) * Option.get! (State.felts st { name := "%2" }) +
                Option.get! (State.felts st { name := "%34" }) +
              Option.get! (State.felts st { name := "%32" }))[felts][{ name := "%39" }] ←
          (Option.get! (State.felts st { name := "%35" }) * Option.get! (State.felts st { name := "%2" }) +
                Option.get! (State.felts st { name := "%34" }) +
              Option.get! (State.felts st { name := "%32" })) *
            Option.get!
              (State.felts st
                {
                  name :=
                    "%1" })) 

-- Run the whole program by using part9_state rather than Code.part9
def part9_state_update (st: State): State :=
  Γ (part9_state st) ⟦Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part9_state for Code.part9 produces the same result
lemma part9_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part9_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part9
  MLIR
  unfold part9_state_update part9_state
  rewrite [←eq]
  rfl

lemma part9_updates_opaque {st : State} : 
  Code.getReturn (part8_state_update st) ↔
  Code.getReturn (part9_state_update (part8_state st)) := by
  simp [part8_state_update, part9_wp]

end Risc0.ComputeDecode.Constraints.WP