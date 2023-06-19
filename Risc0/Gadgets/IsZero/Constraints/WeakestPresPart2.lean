import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart1

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₂ on st
def part₂_state (st: State) : State := 
  (State.updateFelts
  (st["if out[0] then eqz x"] ←ₛ
    some
      (Lit.Constraint
        (Option.get! (State.props st { name := "true" }) ∧
          if Option.get! (State.felts st { name := "out[0]" }) = 0 then True
          else Option.get! (State.props st { name := "andEqz x" }))))
  { name := "1 - out[0]" }
  (Option.get! (State.felts st { name := "1" }) -
   Option.get! (State.felts st { name := "out[0]" })))["out[1]"] ←ₛ getImpl st { name := "output" } 0 1

-- Run the whole program by using part₂_state rather than Code.part₂
def part₂_state_update (st: State): State :=
  Γ (part₂_state st) ⟦Code.part₃; Code.part₄⟧

-- Prove that substituting part₂_state for Code.part₂ produces the same result
lemma part₂_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₂; Code.part₃; Code.part₄) st) ↔
  Code.getReturn (part₂_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₃; Code.part₄) = prog
  unfold Code.part₂
  MLIR
  unfold part₂_state_update part₂_state
  rewrite [←eq]
  rfl

lemma part₂_updates_opaque {st : State} : 
  Code.getReturn (part₁_state_update st) ↔
  Code.getReturn (part₂_state_update (part₁_state st)) := by
  simp [part₁_state_update, part₂_wp]

end Risc0.IsZero.Constraints.WP
