import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart1

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₂ on st
def part₂_state (st: State) : State := State.set!
            (State.updateFelts
              (State.updateFelts
                (State.set! st { name := "output" } 1 (st.felts.get! ⟨"input == 1"⟩))
                { name := "input - 2" }
                (Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" })))
              { name := "input == 2" }
              (if
                  Option.get!
                      (State.felts
                        (State.updateFelts
                          (State.set! st { name := "output" } 1 (st.felts.get! ⟨"input == 1"⟩))
                          { name := "input - 2" }
                          (Option.get! (State.felts st { name := "input" }) -
                            Option.get! (State.felts st { name := "2" })))
                        { name := "input - 2" }) =
                    0 then
                1
              else 0))
            { name := "output" } 2
            (if
                Option.get!
                    (State.felts
                      (State.updateFelts
                        (State.set! st { name := "output" } 1 (st.felts.get! ⟨"input == 1"⟩))
                        { name := "input - 2" }
                        (Option.get! (State.felts st { name := "input" }) -
                          Option.get! (State.felts st { name := "2" })))
                      { name := "input - 2" }) =
                  0 then
              1
            else 0)

-- Run the program from part₂ onwards by using part₂_state rather than Code.part₂
def part₂_state_update (st: State): State :=
  Γ (part₂_state st) ⟦Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₂_state for Code.part₂ produces the same result
-- ****************************** WEAKEST PRE - Part₂ ******************************
lemma part₂_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₂
  MLIR
  rewrite [←eq]
  unfold part₂_state_update part₂_state
  rfl
-- ****************************** WEAKEST PRE - Part₂ ******************************

lemma part₂_updates_opaque {st : State} : 
  (part₁_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂_state_update (part₁_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₁_state_update, part₂_wp]

end Risc0.OneHot.Witness.WP
