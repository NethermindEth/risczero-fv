import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart5

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part6 on st
def part6_state (st: State) : State := 
  
        ((((st[felts][{ name := "%24" }] ←
                Option.get! (State.felts st { name := "%23" }) +
                  Option.get! (State.felts st { name := "%21" }))[felts][{ name := "%25" }] ←
              (Option.get! (State.felts st { name := "%23" }) + Option.get! (State.felts st { name := "%21" })) *
                Option.get! (State.felts st { name := "%3" }))[felts][{ name := "%26" }] ←
            (Option.get! (State.felts st { name := "%23" }) + Option.get! (State.felts st { name := "%21" })) *
                Option.get! (State.felts st { name := "%3" }) +
              Option.get! (State.felts st { name := "%11" }))[felts][{ name := "%27" }] ←
          Option.get! (State.felts st { name := "%10" }) -
            ((Option.get! (State.felts st { name := "%23" }) + Option.get! (State.felts st { name := "%21" })) *
                Option.get! (State.felts st { name := "%3" }) +
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%11" }))) 

-- Run the whole program by using part6_state rather than Code.part6
def part6_state_update (st: State): State :=
  Γ (part6_state st) ⟦Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part6_state for Code.part6 produces the same result
lemma part6_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part6_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part6
  MLIR
  unfold part6_state_update part6_state
  rewrite [←eq]
  rfl

lemma part6_updates_opaque {st : State} : 
  Code.getReturn (part5_state_update st) ↔
  Code.getReturn (part6_state_update (part5_state st)) := by
  simp [part5_state_update, part6_wp]

end Risc0.ComputeDecode.Constraints.WP