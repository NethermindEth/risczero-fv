import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₁ on st
def part₁_state (st: State) : State := State.updateFelts
          (State.updateFelts
            (State.set!
              (State.updateFelts st { name := "input == 0" }
                (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
              { name := "output" } 0 (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
            { name := "input - 1" }
            (Option.get!
                (State.felts
                  (State.updateFelts st { name := "input == 0" }
                    (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
                  { name := "input" }) -
              Option.get!
                (State.felts
                  (State.updateFelts st { name := "input == 0" }
                    (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
                  { name := "1" })))
          { name := "input == 1" }
          (if
              Option.get!
                  (State.felts
                    (State.updateFelts
                      (State.set!
                        (State.updateFelts st { name := "input == 0" }
                          (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
                        { name := "output" } 0 (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
                      { name := "input - 1" }
                      (Option.get!
                          (State.felts
                            (State.updateFelts st { name := "input == 0" }
                              (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
                            { name := "input" }) -
                        Option.get!
                          (State.felts
                            (State.updateFelts st { name := "input == 0" }
                              (if Option.get! (State.felts st { name := "input" }) = 0 then 1 else 0))
                            { name := "1" })))
                    { name := "input - 1" }) =
                0 then
            1
          else 0)

-- Run the program from part₁ onwards by using part₁_state rather than Witness.part₁
def part₁_state_update (st: State): State :=
  Γ (part₁_state st) ⟦Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆⟧

-- ****************************** WEAKEST PRE - Part₁ ******************************
lemma part₁_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆) st).lastOutput = [y₁, y₂, y₃] ↔
  State.lastOutput (part₁_state_update st) = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆) = prog
  unfold Witness.part₁
  MLIR
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₁ ******************************

-- Prove that substituting part₁_state for Witness.part₁ produces the same result
lemma part₁_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₁_state_update st).lastOutput = [y₁, y₂, y₃] := by
  simp only [part₁_state, part₁_state_update, MLIR.runProgram]
  unfold Witness.part₁
  MLIR

end Witness

end Risc0.OneHot.WP