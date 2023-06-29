import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart13

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part14 on st
def part14_state (st: State) : State := 
  
        ((((st[felts][{ name := "%56" }] ←
                Option.get! (State.felts st { name := "%55" }) +
                  Option.get! (State.felts st { name := "%44" }))[felts][{ name := "%57" }] ←
              Option.get! (State.felts st { name := "%8" }) -
                (Option.get! (State.felts st { name := "%55" }) +
                  Option.get! (State.felts st { name := "%44" })))[props][{ name := "%58" }] ←
            (Option.get! (State.props st { name := "%43" }) ∧
              Option.get! (State.felts st { name := "%8" }) -
                  (Option.get! (State.felts st { name := "%55" }) + Option.get! (State.felts st { name := "%44" })) =
                0))["%59"] ←ₛ
          getImpl st { name := "data" } 0 17) 

-- Run the whole program by using part14_state rather than Code.part14
def part14_state_update (st: State): State :=
  Γ (part14_state st) ⟦Code.part15; Code.part16⟧

-- Prove that substituting part14_state for Code.part14 produces the same result
lemma part14_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part14; Code.part15; Code.part16) st) ↔
  Code.getReturn (part14_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part15; Code.part16) = prog
  unfold Code.part14
  MLIR
  unfold part14_state_update part14_state
  rewrite [←eq]
  rfl

lemma part14_updates_opaque {st : State} : 
  Code.getReturn (part13_state_update st) ↔
  Code.getReturn (part14_state_update (part13_state st)) := by
  simp [part13_state_update, part14_wp]

end Risc0.ComputeDecode.Constraints.WP