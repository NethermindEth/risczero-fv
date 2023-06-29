import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart6

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part7 on st
def part7_state (st: State) : State := 
  
        ((((st[props][{ name := "%28" }] ←
                (Option.get! (State.props st { name := "%6" }) ∧
                  Option.get! (State.felts st { name := "%27" }) = 0))["%29"] ←ₛ
              getImpl st { name := "data" } 0 3)["%30"] ←ₛ
            getImpl
              (st[props][{ name := "%28" }] ←
                (Option.get! (State.props st { name := "%6" }) ∧ Option.get! (State.felts st { name := "%27" }) = 0))
              { name := "data" } 0 4)[felts][{ name := "%31" }] ←
          Option.get!
              (State.felts
                ((st[props][{ name := "%28" }] ←
                    (Option.get! (State.props st { name := "%6" }) ∧
                      Option.get! (State.felts st { name := "%27" }) = 0))["%30"] ←ₛ
                  getImpl
                    (st[props][{ name := "%28" }] ←
                      (Option.get! (State.props st { name := "%6" }) ∧
                        Option.get! (State.felts st { name := "%27" }) = 0))
                    { name := "data" } 0 4)
                { name := "%30" }) *
            Option.get!
              (State.felts st
                {
                  name :=
                    "%4" })) 

-- Run the whole program by using part7_state rather than Code.part7
def part7_state_update (st: State): State :=
  Γ (part7_state st) ⟦Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16⟧

-- Prove that substituting part7_state for Code.part7 produces the same result
lemma part7_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part7_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16) = prog
  unfold Code.part7
  MLIR
  unfold part7_state_update part7_state
  rewrite [←eq]
  rfl

lemma part7_updates_opaque {st : State} : 
  Code.getReturn (part6_state_update st) ↔
  Code.getReturn (part7_state_update (part6_state st)) := by
  simp [part6_state_update, part7_wp]

end Risc0.ComputeDecode.Constraints.WP