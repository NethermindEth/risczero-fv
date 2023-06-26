import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart1

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₂ on st
def part₂_state (st: State) : State := 
  let one := 0
  let true_ := 2
  let out0 := 4
  let andEqzX := 5
  let ifOut0ThenEqzX := 6
  let oneMinusOut0 := 7
  let out1 := 8
  (State.updateFelts
  (st[ifOut0ThenEqzX] ←ₛ
    some
      (Lit.Constraint
        (Option.get! (State.props st { name := true_ }) ∧
          if Option.get! (State.felts st { name := out0 }) = 0 then True
          else Option.get! (State.props st { name := andEqzX }))))
  { name := oneMinusOut0 }
  (Option.get! (State.felts st { name := one }) -
   Option.get! (State.felts st { name := out0 })))[out1] ←ₛ getImpl st { name := Output } 0 1

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
