import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart2

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₃ on st
def part₃_state (st: State) : State :=
  if Option.get! st.felts[({ name := "arg1[0]" } : FeltVar)]! = 0
  then st
  else withEqZero (Option.get! st.felts[({ name := "x" } : FeltVar)]!) st

-- Run the program from part₃ onwards by using part₃_state rather than Code.part₃
def part₃_state_update (st: State): State :=
  Γ (part₃_state st) ⟦Code.part₄; Code.part₅⟧

-- Prove that substituting part₃_state for Code.part₃ produces the same result
lemma part₃_wp {st : State} {y₁ y₂ : Option Felt} :
  (MLIR.runProgram (Code.part₃; Code.part₄; Code.part₅) st).lastOutput = [y₁, y₂] ↔
  (part₃_state_update st).lastOutput = [y₁, y₂] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₄; Code.part₅) = prog
  unfold Code.part₃
  MLIR
  rewrite [←eq]
  unfold part₃_state_update part₃_state
  rfl

lemma part₃_updates_opaque {st : State} : 
  (part₂_state_update st).lastOutput = [y₁, y₂] ↔
  (part₃_state_update (part₂_state st)).lastOutput = [y₁, y₂] := by
  simp [part₂_state_update, part₃_wp]

end Risc0.IsZero.Witness.WP
