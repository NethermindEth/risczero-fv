import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart6

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₇ on st
def part₇_state {x: IsNondet} (st: State) : State := {
          buffers :=
            (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).buffers,
          bufferWidths :=
            (st["output[0]AddOutput[1]"] ←ₛ
                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).bufferWidths,
          constraints :=
            (Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                        { name := "1 - Output[2]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "output[2]" })))
                      { name := "output[2]" }) =
                  0 ∨
                Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                        { name := "1 - Output[2]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "output[2]" })))
                      { name := "1 - Output[2]" }) =
                  0) ::
              (st["output[0]AddOutput[1]"] ←ₛ
                  Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).constraints,
          cycle :=
            (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).cycle,
          felts :=
            (State.updateFelts
                (State.updateFelts
                  (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                  { name := "1 - Output[2]" }
                  (Option.get!
                      (State.felts
                        (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                        { name := "1" }) -
                    Option.get!
                      (State.felts
                        (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                        { name := "output[2]" })))
                { name := "output[2] <= 1" }
                (Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                        { name := "1 - Output[2]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "output[2]" })))
                      { name := "output[2]" }) *
                  Option.get!
                    (State.felts
                      (State.updateFelts
                        (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                        { name := "1 - Output[2]" }
                        (Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "1" }) -
                          Option.get!
                            (State.felts
                              (st["output[0]AddOutput[1]"] ←ₛ
                                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ)
                              { name := "output[2]" })))
                      { name := "1 - Output[2]" }))).felts,
          isFailed :=
            (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).isFailed,
          props :=
            (st["output[0]AddOutput[1]"] ←ₛ Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).props,
          vars :=
            (st["output[0]AddOutput[1]"] ←ₛ
                Γ st ⟦@Op.Add x { name := "output[0]" } { name := "output[1]" }⟧ₑ).vars }

-- Run the program from part₇ onwards by using part₇_state rather than Witness.part₇
def part₇_state_update (st: State): State :=
  Γ (@part₇_state IsNondet.NotInNondet st) ⟦Witness.part₈⟧

-- ****************************** WEAKEST PRE - Part₇ ******************************
lemma part₇_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₇_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₈) = prog
  unfold Witness.part₇
  MLIR
  rewrite [←eq]
  unfold part₇_state_update part₇_state
  rfl
-- ****************************** WEAKEST PRE - Part₇ ******************************


-- Prove that substituting part₇_state for Witness.part₇ produces the same result
lemma part₇_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₇_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  unfold Witness.part₇
  MLIR
  unfold part₇_state_update part₇_state
  rfl

lemma part₇_updates_opaque {st : State} : 
  (part₆_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₇_state_update (part₆_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₆_state_update, part₇_updates]

end Witness

end Risc0.OneHot.WP