import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Code

namespace Risc0.OneHot.WP

open MLIRNotation
open Code

namespace Witness

-- The state obtained by running Witness.part₀ on st
def part₀_state (st: State) : State :=
  ((State.updateFelts (State.updateFelts (State.updateFelts st ⟨"2"⟩ 2) ⟨"1"⟩ 1) ⟨"0"⟩ 0)["input"] ←ₛ
    if
      0 ≤ st.cycle ∧
      ⟨"input"⟩ ∈ st.vars ∧
      0 < st.bufferWidths.get! ⟨"input"⟩ ∧
      ((st.buffers.get! ⟨"input"⟩).get! (st.cycle - Back.toNat 0, 0)).isSome = true
    then
      some (Lit.Val (((st.buffers.get! ⟨"input"⟩).get! (st.cycle - Back.toNat 0, 0)).get!))
    else
      none
  )

-- ****************************** WEAKEST PRE - Part₀ ******************************
lemma is0_witness_part₀ {st : State} {y₁ y₂ y₃ : Option Felt} :
  Witness.run st = [y₁, y₂, y₃] ↔
  State.lastOutput (Γ (part₀_state st) ⟦Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅⟧) = [y₁, y₂, y₃] := by
  unfold Witness.run MLIR.runProgram; simp only
  rewrite [Witness.parts_combine]; unfold Witness.parts_combined
  generalize eq : (Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅) = prog
  unfold Witness.part₀
  MLIR
  rewrite [←eq]
  rfl
-- ****************************** WEAKEST PRE - Part₀ ******************************

def part₀_state_update (st: State): State :=
  Γ (part₀_state st) ⟦Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅⟧

lemma part₀_updates {y₁ y₂ y₃: Option Felt} (st : State) :
  (MLIR.runProgram (Witness.part₀; Witness.part₁; Witness.part₂; Witness.part₃; Witness.part₄; Witness.part₅) st).lastOutput = [y₁, y₂, y₃] ↔
  (part₀_state_update st).lastOutput = [y₁, y₂, y₃] := by
  simp only [part₀_state, part₀_state_update, MLIR.runProgram]
  unfold Witness.part₀
  MLIR
  rfl

end Witness

end Risc0.OneHot.WP