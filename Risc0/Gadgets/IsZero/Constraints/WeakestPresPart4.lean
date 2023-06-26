import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart3

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₄ on st
def part₄_state (st: State) : State := 
  let ifOut0ThenEqzX := 6
  let oneMinusOut0 := 7
  let otherCond := 11
  let ifOtherCond := 12
  st[ifOtherCond] ←ₛ
    some
      (Lit.Constraint
        (Option.get! (State.props st { name := ifOut0ThenEqzX }) ∧
          if Option.get! (State.felts st { name := oneMinusOut0 }) = 0 then True
          else Option.get! (State.props st { name := otherCond })))

-- Prove that substituting part₄_state for Code.part₆ produces the same result
lemma part₄_wp {st : State} :
  Code.getReturn (MLIR.runProgram Code.part₄ st) ↔
  Code.getReturn (part₄_state st) := by
  unfold MLIR.runProgram; simp only
  unfold Code.part₄
  MLIR
  unfold part₄_state
  rfl

lemma part₄_updates_opaque {st : State} : 
  Code.getReturn (part₃_state_update st) ↔
  Code.getReturn (part₄_state (part₃_state st)) := by
  simp [part₃_state_update, part₄_wp]

end Risc0.IsZero.Constraints.WP
