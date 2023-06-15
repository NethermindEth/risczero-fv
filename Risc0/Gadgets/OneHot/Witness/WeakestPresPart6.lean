import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart5

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₆ on st
def part₆_state (st: State) : State := {
  buffers := st.buffers,
  bufferWidths := st.bufferWidths,
          constraints :=
            (Option.get!
                    (State.felts
                      (State.updateFelts st { name := "1 - Output[1]" }
                        (Option.get! (State.felts st { name := "1" }) -
                          Option.get! (State.felts st { name := "output[1]" })))
                      { name := "output[1]" }) =
                  0 ∨
                Option.get!
                    (State.felts
                      (State.updateFelts st { name := "1 - Output[1]" }
                        (Option.get! (State.felts st { name := "1" }) -
                          Option.get! (State.felts st { name := "output[1]" })))
                      { name := "1 - Output[1]" }) =
                  0) ::
              st.constraints,
          cycle := st.cycle,
          felts :=
            (State.updateFelts
                (State.updateFelts st { name := "1 - Output[1]" }
                  (Option.get! (State.felts st { name := "1" }) - Option.get! (State.felts st { name := "output[1]" })))
                { name := "output[1] <= 1" }
                (Option.get!
                    (State.felts
                      (State.updateFelts st { name := "1 - Output[1]" }
                        (Option.get! (State.felts st { name := "1" }) -
                          Option.get! (State.felts st { name := "output[1]" })))
                      { name := "output[1]" }) *
                  Option.get!
                    (State.felts
                      (State.updateFelts st { name := "1 - Output[1]" }
                        (Option.get! (State.felts st { name := "1" }) -
                          Option.get! (State.felts st { name := "output[1]" })))
                      { name := "1 - Output[1]" }))).felts,
          isFailed := st.isFailed, props := st.props, vars := st.vars }

-- Run the program from part₆ onwards by using part₆_state rather than Witness.part₆
def part₆_state_update (st: State): State :=
  Γ (part₆_state st) ⟦Witness.part₇; Witness.part₈⟧

-- ****************************** WEAKEST PRE - Part₆ ******************************
lemma part₆_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Witness.part₆; Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₆_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₇; Witness.part₈) = prog
  unfold Witness.part₆
  MLIR
  rewrite [←eq]
  unfold part₆_state_update part₆_state
  rfl
-- ****************************** WEAKEST PRE - Part₆ ******************************


-- Prove that substituting part₆_state for Witness.part₆ produces the same result
lemma part₆_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₆; Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₆_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₇; Witness.part₈) = prog
  unfold Witness.part₆
  MLIR
  rewrite [←eq]
  unfold part₆_state_update part₆_state
  rfl

lemma part₆_updates_opaque {st : State} : 
  (part₅_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₆_state_update (part₅_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₅_state_update, part₆_updates]

end Witness

end Risc0.OneHot.WP