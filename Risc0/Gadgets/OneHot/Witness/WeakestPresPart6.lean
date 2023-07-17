import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart5

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₆ on st
def part₆_state (st: State) : State :=
  (withEqZero
          (Option.get! (State.felts st { name := "output[1]" }) *
            (Option.get! (State.felts st { name := "1" }) - Option.get! (State.felts st { name := "output[1]" })))
          ((st[felts][{ name := "1 - Output[1]" }] ←
              Option.get! (State.felts st { name := "1" }) -
                Option.get! (State.felts st { name := "output[1]" }))[felts][{ name := "output[1] <= 1" }] ←
            Option.get! (State.felts st { name := "output[1]" }) *
              (Option.get! (State.felts st { name := "1" }) -
                Option.get! (State.felts st { name := "output[1]" }))))

-- Run the program from part₆ onwards by using part₆_state rather than Code.part₆
def part₆_state_update (st: State): State :=
  Γ (part₆_state st) ⟦Code.part₇; Code.part₈⟧

-- Prove that substituting part₆_state for Code.part₆ produces the same result
lemma part₆_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₆_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₇; Code.part₈) = prog
  unfold Code.part₆
  MLIR
  rewrite [←eq]
  unfold part₆_state_update part₆_state
  rfl

lemma part₆_updates_opaque {st : State} : 
  (part₅_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₆_state_update (part₅_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₅_state_update, part₆_wp]

end Risc0.OneHot.Witness.WP
