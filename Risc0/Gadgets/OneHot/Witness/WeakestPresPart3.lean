import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Witness.Code
import Risc0.Gadgets.OneHot.Witness.WeakestPresPart2

namespace Risc0.OneHot.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₃ on st
def part₃_state (st: State) : State :=
  ((st["output[1]"] ←ₛ getImpl st { name := "output" } 0 1)["output[2]"] ←ₛ
          getImpl st { name := "output" } 0 2)

-- Run the program from part₃ onwards by using part₃_state rather than Code.part₃
def part₃_state_update (st: State): State :=
  Γ (part₃_state st) ⟦Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈⟧

-- Prove that substituting part₃_state for Code.part₃ produces the same result
lemma part₃_wp {st : State} {y₁ y₂ y₃ : Option Felt} :
  (MLIR.runProgram (Code.part₃; Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₃_state_update st).lastOutput = [y₁, y₂, y₃] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₄; Code.part₅; Code.part₆; Code.part₇; Code.part₈) = prog
  unfold Code.part₃
  MLIR
  rewrite [←eq]
  unfold part₃_state_update part₃_state
  rfl

lemma part₃_updates_opaque {st : State} : 
  (part₂_state_update st).lastOutput = [y₁, y₂, y₃] ↔
  (part₃_state_update (part₂_state st)).lastOutput = [y₁, y₂, y₃] := by
  simp [part₂_state_update, part₃_wp]

end Risc0.OneHot.Witness.WP
