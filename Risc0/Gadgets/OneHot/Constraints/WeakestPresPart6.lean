import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart5

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₆ on st
def part₆_state (st: State) : State :=
  ((((st[props][{ name := "andEqz output[2]<=1" }] ←
            (Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
              Option.get! (State.felts st { name := "output[2]<=1" }) = 0))[felts][{ name := "outputSum" }] ←
          Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
            Option.get! (State.felts st { name := "output[2]" }))[felts][{ name := "outputSum-1" }] ←
        Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
            Option.get! (State.felts st { name := "output[2]" }) -
          Option.get! (State.felts st { name := "1" }))[props][{ name := "andEqz outputSum-1" }] ←
      ((Option.get! (State.props st { name := "andEqz output[1]<=1" }) ∧
          Option.get! (State.felts st { name := "output[2]<=1" }) = 0) ∧
        Option.get! (State.felts st { name := "output[0]+Output[1]" }) +
              Option.get! (State.felts st { name := "output[2]" }) -
            Option.get! (State.felts st { name := "1" }) =
          0))

-- Prove that substituting part₆_state for Code.part₆ produces the same result
lemma part₆_wp {st : State} :
  Code.getReturn (MLIR.runProgram Code.part₆ st) ↔
  Code.getReturn (part₆_state st) := by
  unfold MLIR.runProgram; simp only
  unfold Code.part₆
  MLIR
  unfold part₆_state
  rfl

lemma part₆_updates_opaque {st : State} : 
  Code.getReturn (part₅_state_update st) ↔
  Code.getReturn (part₆_state (part₅_state st)) := by
  simp [part₅_state_update, part₆_wp]

end Risc0.OneHot.Constraints.WP
