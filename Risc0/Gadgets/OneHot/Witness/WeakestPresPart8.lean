import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart7

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₈ on st
def part₈_state (st: State) : State :=
  (withEqZero
        (Option.get! (State.felts st { name := "output[0]AddOutput[1]" }) +
            Option.get! (State.felts st { name := "output[2]" }) -
          Option.get! (State.felts st { name := "1" }))
        ((st[felts][{ name := "outputSum" }] ←
            Option.get! (State.felts st { name := "output[0]AddOutput[1]" }) +
              Option.get! (State.felts st { name := "output[2]" }))[felts][{ name := "outputSum - 1" }] ←
          Option.get! (State.felts st { name := "output[0]AddOutput[1]" }) +
              Option.get! (State.felts st { name := "output[2]" }) -
            Option.get! (State.felts st { name := "1" })))

-- Prove that substituting part₈_state for Code.part₈ produces the same result
lemma part₈_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram Code.part₈ st).lastOutput = [y₁, y₂, y₃] ↔
  (part₈_state st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  unfold Code.part₈
  MLIR
  unfold part₈_state
  rfl

lemma part₈_updates_opaque {st : State} : 
  (part₇_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₈_state (part₇_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₇_state_update, part₈_wp]

end Risc0.OneHot.Witness.WP
