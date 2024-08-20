import Risc0.Cirgen
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart3

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₄ on st
def part₄_state (st: State) : State :=
  (withEqZero
          (Option.get! (State.felts st { name := "output[1]" }) +
              Option.get! (State.felts st { name := "output[2]" }) * Option.get! (State.felts st { name := "2" }) -
            Option.get! (State.felts st { name := "input" }))
          (((st[felts][{ name := "output[2] * 2" }] ←
                Option.get! (State.felts st { name := "output[2]" }) *
                  Option.get! (State.felts st { name := "2" }))[felts][{ name := "2*output[2]+output[1]" }] ←
              Option.get! (State.felts st { name := "output[1]" }) +
                Option.get! (State.felts st { name := "output[2]" }) *
                  Option.get! (State.felts st { name := "2" }))[felts][{ name := "2*output[2]+output[1] - input" }] ←
            Option.get! (State.felts st { name := "output[1]" }) +
                Option.get! (State.felts st { name := "output[2]" }) * Option.get! (State.felts st { name := "2" }) -
              Option.get! (State.felts st { name := "input" })))

-- Run the program from part₄ onwards by using part₄_state rather than Code.part₄
def part₄_state_update (st: State): State :=
  Γ (part₄_state st) ⟦Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₄_state for Code.part₄ produces the same result
lemma part₄_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₄_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₄
  MLIR
  rewrite [←eq]
  unfold part₄_state_update part₄_state
  rfl

lemma part₄_updates_opaque {st : State} : 
  (part₃_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₄_state_update (part₃_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₃_state_update, part₄_wp]

end Risc0.OneHot.Witness.WP
