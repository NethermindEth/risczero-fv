import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart2

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₃ on st
def part₃_state (st: State) : State := 
  (State.updateFelts
          (State.updateFelts st { name := "x * out[1]" }
            (Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" })))
          { name := "x * out[1] - 1" }
          (Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" }) -
            Option.get!
              (State.felts
                (State.updateFelts st { name := "x * out[1]" }
                  (Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" })))
                { name := "1" })))["other cond"] ←ₛ
        some
          (Lit.Constraint
            (Option.get! (State.props st { name := "true" }) ∧
              Option.get! (State.felts st { name := "x" }) * Option.get! (State.felts st { name := "out[1]" }) -
                  Option.get!
                    (State.felts
                      (State.updateFelts st { name := "x * out[1]" }
                        (Option.get! (State.felts st { name := "x" }) *
                          Option.get! (State.felts st { name := "out[1]" })))
                      { name := "1" }) =
                0))

-- Run the whole program by using part₃_state rather than Code.part₃
def part₃_state_update (st: State): State :=
  Γ (part₃_state st) ⟦Code.part₄⟧

-- Prove that substituting part₃_state for Code.part₃ produces the same result
lemma part₃_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₃; Code.part₄) st) ↔
  Code.getReturn (part₃_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : Code.part₄ = prog
  unfold Code.part₃
  MLIR
  unfold part₃_state_update part₃_state
  rewrite [←eq]
  rfl

lemma part₃_updates_opaque {st : State} : 
  Code.getReturn (part₂_state_update st) ↔
  Code.getReturn (part₃_state_update (part₂_state st)) := by
  simp [part₂_state_update, part₃_wp]

end Risc0.IsZero.Constraints.WP
