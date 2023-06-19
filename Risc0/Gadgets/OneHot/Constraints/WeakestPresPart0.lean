import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₀ on st
def part₀_state (st: State) : State := {
  buffers := st.buffers,
  bufferWidths := st.bufferWidths,
  constraints := st.constraints,
  cycle := st.cycle,
  felts := (State.updateFelts (State.updateFelts st { name := "1" } 1) { name := "2" } 2).felts,
  isFailed := st.isFailed,
  props := st.props[{ name := "true" }] ←ₘ True,
  vars := st.vars }["input"] ←ₛ
    if
      0 ≤ st.cycle ∧
      { name := "input" } ∈ st.vars ∧
      0 < Map.get! st.bufferWidths { name := "input" } ∧
      Option.isSome (Buffer.get! (Map.get! st.buffers { name := "input" }) (st.cycle - Back.toNat 0, 0)) =
      true
    then
      some (Lit.Val (Option.get! (Buffer.get! (Map.get! st.buffers { name := "input" }) (st.cycle - Back.toNat 0, 0))))
    else
      none

-- Run the whole program by using part₀_state rather than Code.part₀
def part₀_state_update (st: State): State :=
  Γ (part₀_state st) ⟦Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₀_state for Code.part₀ produces the same result
-- ****************************** WEAKEST PRE - Part₀ ******************************
lemma part₀_wp {st : State} :
  Code.run st ↔
  Code.getReturn (part₀_state_update st) := by
  unfold Code.run MLIR.runProgram; simp only
  rewrite [Code.parts_combine]; unfold Code.parts_combined
  generalize eq : (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₀
  MLIR
  unfold part₀_state_update part₀_state
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₀ ******************************

end Risc0.OneHot.Constraints.WP
