import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart4

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part5 on st
def part5_state (st: State) : State := 
  
        ((((st[felts][{ name := "%20" }] ←
                Option.get! (State.felts st { name := "%19" }) +
                  Option.get! (State.felts st { name := "%14" }))[felts][{ name := "%21" }] ←
              Option.get! (State.felts st { name := "%19" }) + Option.get! (State.felts st { name := "%14" }) +
                Option.get! (State.felts st { name := "%12" }))["%22"] ←ₛ
            getImpl st { name := "data" } 0 10)[felts][{ name := "%23" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%20" }] ←
                      Option.get! (State.felts st { name := "%19" }) +
                        Option.get! (State.felts st { name := "%14" }))[felts][{ name := "%21" }] ←
                    Option.get! (State.felts st { name := "%19" }) + Option.get! (State.felts st { name := "%14" }) +
                      Option.get! (State.felts st { name := "%12" }))["%22"] ←ₛ
                  getImpl st { name := "data" } 0 10)
                { name := "%22" }) *
            Option.get!
              (State.felts st
                {
                  name :=
                    "%5" })) 

-- Run the whole program by using part5_state rather than Code.part5
def part5_state_update (st: State): State :=
  Γ (part5_state st) ⟦Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part5_state for Code.part5 produces the same result
lemma part5_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part5_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part5
  MLIR
  unfold part5_state_update part5_state
  rewrite [←eq]
  rfl

lemma part5_updates_opaque {st : State} : 
  Code.getReturn (part4_state_update st) ↔
  Code.getReturn (part5_state_update (part4_state st)) := by
  simp [part4_state_update, part5_wp]

end Risc0.ComputeDecode.Constraints.WP