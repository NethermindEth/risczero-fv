import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart7

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₈ on st
def part₈_state {x: IsNondet} (st: State) : State := {
        buffers :=
          (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).buffers,
        bufferWidths :=
          (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).bufferWidths,
        constraints :=
          (Option.get!
                  (State.felts
                    (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ)
                    { name := "outputSum" }) -
                Option.get!
                  (State.felts
                    (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ)
                    { name := "1" }) =
              0) ::
            (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).constraints,
        cycle := (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).cycle,
        felts :=
          (State.updateFelts
              (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ)
              { name := "outputSum - 1" }
              (Option.get!
                  (State.felts
                    (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ)
                    { name := "outputSum" }) -
                Option.get!
                  (State.felts
                    (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ)
                    { name := "1" }))).felts,
        isFailed :=
          (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).isFailed,
        props := (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).props,
        vars := (st["outputSum"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]AddOutput[1]" } { name := "output[2]" }⟧ₑ).vars }

-- part₈_state_update would be exactly part₈_state, since there is no remaining program to run afterwards

-- ****************************** WEAKEST PRE - Part₈ ******************************
lemma part₈_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram Witness.part₈ st).lastOutput = [y₁, y₂, y₃] ↔
  (@part₈_state IsNondet.NotInNondet st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  unfold Witness.part₈
  MLIR
  unfold part₈_state
  rfl
-- ****************************** WEAKEST PRE - Part₈ ******************************


-- Prove that substituting part₈_state for Witness.part₈ produces the same result
lemma part₈_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram Witness.part₈ st).lastOutput = [y₁, y₂, y₃] ↔
  (@part₈_state IsNondet.NotInNondet st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  unfold Witness.part₈
  MLIR
  unfold part₈_state
  rfl

lemma part₈_updates_opaque {st : State} : 
  (part₇_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (@part₈_state IsNondet.NotInNondet (@part₇_state IsNondet.NotInNondet st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₇_state_update, part₈_updates]

end Witness

end Risc0.OneHot.WP