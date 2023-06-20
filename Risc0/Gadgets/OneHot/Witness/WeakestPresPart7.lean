import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart6

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₇ on st
def part₇_state (st: State) : State :=
  { buffers := st.buffers, bufferWidths := st.bufferWidths,
          constraints :=
            (Option.get!
                    (((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                          Option.get! (State.felts st { name := "output[0]" }) +
                            Option.get! (State.felts st { name := "output[1]" }))[{ name := "1 - Output[2]" }] ←ₘ
                        Option.get!
                            ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                                Option.get! (State.felts st { name := "output[0]" }) +
                                  Option.get! (State.felts st { name := "output[1]" }))
                              { name := "1" }) -
                          Option.get!
                            ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                                Option.get! (State.felts st { name := "output[0]" }) +
                                  Option.get! (State.felts st { name := "output[1]" }))
                              { name := "output[2]" }))
                      { name := "output[2]" }) =
                  0 ∨
                Option.get!
                      ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                          Option.get! (State.felts st { name := "output[0]" }) +
                            Option.get! (State.felts st { name := "output[1]" }))
                        { name := "1" }) -
                    Option.get!
                      ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                          Option.get! (State.felts st { name := "output[0]" }) +
                            Option.get! (State.felts st { name := "output[1]" }))
                        { name := "output[2]" }) =
                  0) ::
              st.constraints,
          cycle := st.cycle,
          felts :=
            ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                  Option.get! (State.felts st { name := "output[0]" }) +
                    Option.get! (State.felts st { name := "output[1]" }))[{ name := "1 - Output[2]" }] ←ₘ
                Option.get!
                    ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) +
                          Option.get! (State.felts st { name := "output[1]" }))
                      { name := "1" }) -
                  Option.get!
                    ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) +
                          Option.get! (State.felts st { name := "output[1]" }))
                      { name := "output[2]" }))[{ name := "output[2] <= 1" }] ←ₘ
              Option.get!
                  (((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) +
                          Option.get! (State.felts st { name := "output[1]" }))[{ name := "1 - Output[2]" }] ←ₘ
                      Option.get!
                          ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                              Option.get! (State.felts st { name := "output[0]" }) +
                                Option.get! (State.felts st { name := "output[1]" }))
                            { name := "1" }) -
                        Option.get!
                          ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                              Option.get! (State.felts st { name := "output[0]" }) +
                                Option.get! (State.felts st { name := "output[1]" }))
                            { name := "output[2]" }))
                    { name := "output[2]" }) *
                (Option.get!
                    ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) +
                          Option.get! (State.felts st { name := "output[1]" }))
                      { name := "1" }) -
                  Option.get!
                    ((st.felts[{ name := "output[0]AddOutput[1]" }] ←ₘ
                        Option.get! (State.felts st { name := "output[0]" }) +
                          Option.get! (State.felts st { name := "output[1]" }))
                      { name := "output[2]" })),
          isFailed := st.isFailed, props := st.props, vars := st.vars }

-- Run the program from part₇ onwards by using part₇_state rather than Code.part₇
def part₇_state_update (st: State): State :=
  Γ (part₇_state st) ⟦Code.part₈⟧

-- Prove that substituting part₇_state for Code.part₇ produces the same result
lemma part₇_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₇_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₈) = prog
  unfold Code.part₇
  MLIR
  rewrite [←eq]
  unfold part₇_state_update part₇_state
  rfl

lemma part₇_updates_opaque {st : State} : 
  (part₆_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₇_state_update (part₆_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₆_state_update, part₇_wp]

end Risc0.OneHot.Witness.WP
