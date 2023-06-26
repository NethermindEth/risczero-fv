import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart1

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₂ on st
def part₂_state (st: State) : State :=
  let arg10 := 4
  st[arg10] ←ₛ getImpl st { name := Output } 0 0

-- Run the program from part₂ onwards by using part₂_state rather than Code.part₂
def part₂_state_update (st: State): State :=
  Γ (part₂_state st) ⟦Code.part₃; Code.part₄; Code.part₅⟧

-- Prove that substituting part₂_state for Code.part₂ produces the same result
lemma part₂_wp {st : State} {y₁ y₂ : Option Felt} :
  (MLIR.runProgram (Code.part₂; Code.part₃; Code.part₄; Code.part₅) st).lastOutput = [y₁, y₂] ↔
  (part₂_state_update st).lastOutput = [y₁, y₂] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₃; Code.part₄; Code.part₅) = prog
  unfold Code.part₂
  MLIR
  rewrite [←eq]
  unfold part₂_state_update part₂_state
  rfl

lemma part₂_updates_opaque {st : State} : 
  (part₁_state_update st).lastOutput = [y₁, y₂] ↔
  (part₂_state_update (part₁_state st)).lastOutput = [y₁, y₂] := by
  simp [part₁_state_update, part₂_wp]

end Risc0.IsZero.Witness.WP
