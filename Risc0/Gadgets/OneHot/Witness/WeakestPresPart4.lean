import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₄ on st
def part₄_state {x: IsNondet} (st: State) : State := {
          buffers :=
            ((State.updateFelts st { name := "output[2] * 2" }
                  (Option.get! (State.felts st { name := "output[2]" }) *
                    Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                Γ
                  (State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get!
                        (State.felts st
                          { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).buffers,
          bufferWidths :=
            ((State.updateFelts st { name := "output[2] * 2" }
                  (Option.get! (State.felts st { name := "output[2]" }) *
                    Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                Γ
                  (State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get!
                        (State.felts st
                          {
                            name :=
                              "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).bufferWidths,
          constraints :=
            (Option.get!
                    (State.felts
                      ((State.updateFelts st { name := "output[2] * 2" }
                          (Option.get! (State.felts st { name := "output[2]" }) *
                            Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                        Γ
                          (State.updateFelts st { name := "output[2] * 2" }
                            (Option.get! (State.felts st { name := "output[2]" }) *
                              Option.get!
                                (State.felts st
                                  { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ)
                      { name := "2*output[2]+output[1]" }) -
                  Option.get!
                    (State.felts
                      ((State.updateFelts st { name := "output[2] * 2" }
                          (Option.get! (State.felts st { name := "output[2]" }) *
                            Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                        Γ
                          (State.updateFelts st { name := "output[2] * 2" }
                            (Option.get! (State.felts st { name := "output[2]" }) *
                              Option.get!
                                (State.felts st
                                  { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ)
                      { name := "input" }) =
                0) ::
              ((State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                  Γ
                    (State.updateFelts st { name := "output[2] * 2" }
                      (Option.get! (State.felts st { name := "output[2]" }) *
                        Option.get!
                          (State.felts st
                            {
                              name :=
                                "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).constraints,
          cycle :=
            ((State.updateFelts st { name := "output[2] * 2" }
                  (Option.get! (State.felts st { name := "output[2]" }) *
                    Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                Γ
                  (State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get!
                        (State.felts st
                          { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).cycle,
          felts :=
            (State.updateFelts
                ((State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                  Γ
                    (State.updateFelts st { name := "output[2] * 2" }
                      (Option.get! (State.felts st { name := "output[2]" }) *
                        Option.get!
                          (State.felts st
                            { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ)
                { name := "2*output[2]+output[1] - input" }
                (Option.get!
                    (State.felts
                      ((State.updateFelts st { name := "output[2] * 2" }
                          (Option.get! (State.felts st { name := "output[2]" }) *
                            Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                        Γ
                          (State.updateFelts st { name := "output[2] * 2" }
                            (Option.get! (State.felts st { name := "output[2]" }) *
                              Option.get!
                                (State.felts st
                                  { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ)
                      { name := "2*output[2]+output[1]" }) -
                  Option.get!
                    (State.felts
                      ((State.updateFelts st { name := "output[2] * 2" }
                          (Option.get! (State.felts st { name := "output[2]" }) *
                            Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                        Γ
                          (State.updateFelts st { name := "output[2] * 2" }
                            (Option.get! (State.felts st { name := "output[2]" }) *
                              Option.get!
                                (State.felts st
                                  { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ)
                      { name := "input" }))).felts,
          isFailed :=
            ((State.updateFelts st { name := "output[2] * 2" }
                  (Option.get! (State.felts st { name := "output[2]" }) *
                    Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                Γ
                  (State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get!
                        (State.felts st
                          { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).isFailed,
          props :=
            ((State.updateFelts st { name := "output[2] * 2" }
                  (Option.get! (State.felts st { name := "output[2]" }) *
                    Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                Γ
                  (State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get!
                        (State.felts st
                          { name := "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).props,
          vars :=
            ((State.updateFelts st { name := "output[2] * 2" }
                  (Option.get! (State.felts st { name := "output[2]" }) *
                    Option.get! (State.felts st { name := "2" })))["2*output[2]+output[1]"] ←ₛ
                Γ
                  (State.updateFelts st { name := "output[2] * 2" }
                    (Option.get! (State.felts st { name := "output[2]" }) *
                      Option.get!
                        (State.felts st
                          {
                            name :=
                              "2" }))) ⟦@Op.Add x { name := "output[1]" } { name := "output[2] * 2" }⟧ₑ).vars }

-- Run the program from part₄ onwards by using part₄_state rather than Witness.part₄
def part₄_state_update (st: State): State :=
  Γ (@part₄_state IsNondet.NotInNondet st) ⟦Witness.part₅; Witness.part₆; Witness.part₇⟧

-- ****************************** WEAKEST PRE - Part₄ ******************************
lemma part₄_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₄_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₅; Witness.part₆; Witness.part₇) = prog
  unfold Witness.part₄
  MLIR
  rewrite [←eq]
  unfold part₄_state_update part₄_state
  rfl
-- ****************************** WEAKEST PRE - Part₃ ******************************


-- Prove that substituting part₃_state for Witness.part₃ produces the same result
lemma part₄_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₄; Witness.part₅; Witness.part₆) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₄_state_update st).lastOutput = [y₁, y₂, y₃] := by
  simp only [part₄_state, part₄_state_update, MLIR.runProgram]
  unfold Witness.part₄
  MLIR
  rfl

end Witness

end Risc0.OneHot.WP