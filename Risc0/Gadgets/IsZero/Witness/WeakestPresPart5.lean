import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart4

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₅ on st
def part₅_state (st: State) : State := 
  if Option.get! st.felts[({ name := "1 - arg1[0]" } : FeltVar)]! = 0
  then st
  else st["arg1[1]"] ←ₛ getImpl st { name := "output" } 0 1

-- Prove that substituting part₅_state for Code.part₅ produces the same result
lemma part₅_wp {st : State} {y₁ y₂ : Option Felt} :
  (MLIR.runProgram Code.part₅ st).lastOutput = [y₁, y₂] ↔
  (part₅_state st).lastOutput = [y₁, y₂] := by
  unfold MLIR.runProgram; simp only
  unfold Code.part₅
  MLIR
  unfold part₅_state
  rfl

lemma part₅_updates_opaque {st : State} : 
  (part₄_state_update st).lastOutput = [y₁, y₂] ↔
  (part₅_state (part₄_state st)).lastOutput = [y₁, y₂] := by
  simp [part₄_state_update, part₅_wp]

end Risc0.IsZero.Witness.WP
