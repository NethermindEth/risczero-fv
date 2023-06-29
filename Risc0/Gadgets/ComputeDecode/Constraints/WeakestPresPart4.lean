import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart3

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part4 on st
def part4_state (st: State) : State := 
  
        ((((st[felts][{ name := "%16" }] ←
                Option.get! (State.felts st { name := "%15" }) *
                  Option.get! (State.felts st { name := "%2" }))["%17"] ←ₛ
              getImpl st { name := "data" } 0 1)[felts][{ name := "%18" }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%16" }] ←
                      Option.get! (State.felts st { name := "%15" }) *
                        Option.get! (State.felts st { name := "%2" }))["%17"] ←ₛ
                    getImpl st { name := "data" } 0 1)
                  { name := "%17" }) *
              Option.get! (State.felts st { name := "%1" }))[felts][{ name := "%19" }] ←
          Option.get!
                (State.felts
                  ((st[felts][{ name := "%16" }] ←
                      Option.get! (State.felts st { name := "%15" }) *
                        Option.get! (State.felts st { name := "%2" }))["%17"] ←ₛ
                    getImpl st { name := "data" } 0 1)
                  { name := "%17" }) *
              Option.get! (State.felts st { name := "%1" }) +
            Option.get! (State.felts st { name := "%15" }) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%2" })) 

-- Run the whole program by using part4_state rather than Code.part4
def part4_state_update (st: State): State :=
  Γ (part4_state st) ⟦Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part4_state for Code.part4 produces the same result
lemma part4_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part4; Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part4_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part5; Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part4
  MLIR
  unfold part4_state_update part4_state
  rewrite [←eq]
  rfl

lemma part4_updates_opaque {st : State} : 
  Code.getReturn (part3_state_update st) ↔
  Code.getReturn (part4_state_update (part3_state st)) := by
  simp [part3_state_update, part4_wp]

end Risc0.ComputeDecode.Constraints.WP