import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Witness.Code
import Risc0.Gadgets.IsZero.Witness.WeakestPresPart3

namespace Risc0.IsZero.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part₄ on st
def part₄_state (st: State) : State := 
  let one := 0
  let arg10 := 4
  let oneMinusArg10 := 5
  st[oneMinusArg10] ←ₛ some (Lit.Val
    (Option.get! (State.felts st { name := one }) -
     Option.get! (State.felts st { name := arg10 })))

-- Run the program from part₄ onwards by using part₄_state rather than Code.part₄
def part₄_state_update (st: State): State :=
  Γ (part₄_state st) ⟦Code.part₅⟧

-- Prove that substituting part₄_state for Code.part₄ produces the same result
lemma part₄_wp {st : State} {y₁ y₂ : Option Felt} :
  (MLIR.runProgram (Code.part₄; Code.part₅) st).lastOutput = [y₁, y₂] ↔
  (part₄_state_update st).lastOutput = [y₁, y₂] := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₅) = prog
  unfold Code.part₄
  MLIR
  rewrite [←eq]
  unfold part₄_state_update part₄_state
  rfl

lemma part₄_updates_opaque {st : State} : 
  (part₃_state_update st).lastOutput = [y₁, y₂] ↔
  (part₄_state_update (part₃_state st)).lastOutput = [y₁, y₂] := by
  simp [part₃_state_update, part₄_wp]

end Risc0.IsZero.Witness.WP
