import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.ComputeDecode.Constraints.Code
import Risc0.Gadgets.ComputeDecode.Constraints.WeakestPresPart15

namespace Risc0.ComputeDecode.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part16 on st
def part16_state (st: State) : State := 
   st[props][{ name := "%64" }] ←
      (Option.get! (State.props st { name := "%58" }) ∧ Option.get! (State.felts st { name := "%63" }) = 0)

-- Prove that substituting part16_state for Code.part16 produces the same result
lemma part16_wp {st : State} :
  Code.getReturn (MLIR.runProgram Code.part16 st) ↔
  Code.getReturn (part16_state st) := by
  unfold MLIR.runProgram; simp only
  unfold Code.part16
  MLIR_single
  unfold part16_state
  rfl

lemma part16_updates_opaque {st : State} : 
  Code.getReturn (part15_state_update st) ↔
  Code.getReturn (part16_state (part15_state st)) := by
  simp [part15_state_update, part16_wp]

end Risc0.ComputeDecode.Constraints.WP