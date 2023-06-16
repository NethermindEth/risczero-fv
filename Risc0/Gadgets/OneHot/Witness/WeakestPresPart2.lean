import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart1

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₂ on st
-- def part₂_state (st: State) : State := State.set!
--             (State.updateFelts
--               (State.updateFelts
--                 (State.set! st { name := "output" } 1 (st.felts.get! ⟨"input == 1"⟩))
--                 { name := "input - 2" }
--                 (Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" })))
--               { name := "input == 2" }
--               (if
--                   Option.get!
--                       (State.felts
--                         (State.updateFelts
--                           (State.set! st { name := "output" } 1 (st.felts.get! ⟨"input == 1"⟩))
--                           { name := "input - 2" }
--                           (Option.get! (State.felts st { name := "input" }) -
--                             Option.get! (State.felts st { name := "2" })))
--                         { name := "input - 2" }) =
--                     0 then
--                 1
--               else 0))
--             { name := "output" } 2
--             (if
--                 Option.get!
--                     (State.felts
--                       (State.updateFelts
--                         (State.set! st { name := "output" } 1 (st.felts.get! ⟨"input == 1"⟩))
--                         { name := "input - 2" }
--                         (Option.get! (State.felts st { name := "input" }) -
--                           Option.get! (State.felts st { name := "2" })))
--                       { name := "input - 2" }) =
--                   0 then
--               1
--             else 0)

def part₂_state (st: State) : State := State.set!
  (State.updateFelts
    (State.updateFelts (State.set! st { name := "output" } 1 (Option.get! st.felts[({ name := "input == 1" } : FeltVar)]!))
      { name := "input - 2" }
      (Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" })))
    { name := "input == 2" }
    (if Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" }) = 0 then
      1
    else 0))
  { name := "output" } 2
  (if Option.get! (State.felts st { name := "input" }) - Option.get! (State.felts st { name := "2" }) = 0 then 1
  else 0)

-- Run the program from part₂ onwards by using part₂_state rather than Witness.part₂
def part₂_state_update (st: State): State :=
  Γ (part₂_state st) ⟦Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈⟧

-- ****************************** WEAKEST PRE - Part₂ ******************************
lemma part₂_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈) = prog
  unfold Witness.part₂
  MLIR
  rewrite [←eq]
  unfold part₂_state_update part₂_state
  rfl
-- ****************************** WEAKEST PRE - Part₂ ******************************

-- Prove that substituting part₂_state for Witness.part₂ produces the same result
lemma part₂_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅; Witness.part₆; Witness.part₇; Witness.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂_state_update st).lastOutput = [y₁, y₂, y₃] := by
  simp only [part₂_state, part₂_state_update, MLIR.runProgram]
  unfold Witness.part₂
  MLIR

lemma part₂_updates_opaque {st : State} : 
  (part₁_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₂_state_update (part₁_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₁_state_update, part₂_updates]

end Witness

end Risc0.OneHot.WP