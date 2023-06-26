import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart0

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₁ on st
def part₁_state (st: State) : State :=
  let x := 1
  let isZeroBit := 2
  let invVal := 3
  State.set! (State.updateFelts (State.set! (State.updateFelts st
    { name := isZeroBit }
    (if Option.get! (State.felts st { name := x }) = 0 then 1 else 0)) { name := Output } 0
    (if Option.get! (State.felts st { name := x }) = 0 then 1 else 0)) { name := invVal }
    (if Option.get! st.felts[({ name := x } : FeltVar)]! = 0 then 0 else (Option.get! st.felts[({ name := x } : FeltVar)]!)⁻¹)) { name := Output } 1
    (if Option.get! st.felts[({ name := x } : FeltVar)]! = 0 then 0 else (Option.get! st.felts[({ name := x } : FeltVar)]!)⁻¹)

-- Run the program from part₁ onwards by using part₁_state rather than Code.part₁
def part₁_state_update (st: State): State :=
  Γ (part₁_state st) ⟦Code.part₂; Code.part₃; Code.part₄; Code.part₅⟧

-- Prove that substituting part₁_state for Code.part₁ produces the same result
lemma part₁_wp {st : State} {y₁ y₂ : Option Felt} :
  (MLIR.runProgram (Code.part₁; Code.part₂; Code.part₃; Code.part₄; Code.part₅) st).lastOutput = [y₁, y₂] ↔
  (part₁_state_update st).lastOutput = [y₁, y₂] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂; Code.part₃; Code.part₄; Code.part₅) = prog
  unfold Code.part₁
  MLIR
  rewrite [←eq]
  unfold part₁_state_update part₁_state
  rfl

lemma part₁_updates_opaque {st : State} : 
  (part₀_state_update st).lastOutput = [y₁, y₂] ↔
  (part₁_state_update (part₀_state st)).lastOutput = [y₁, y₂] := by
  simp [part₀_state_update, part₁_wp]

end Risc0.IsZero.Witness.WP
