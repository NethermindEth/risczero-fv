import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.IsZero.Constraints.Code
import Risc0.Gadgets.IsZero.Constraints.WeakestPresPart0

namespace Risc0.IsZero.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₁ on st
def part₁_state (st: State) : State := 
  ((st["x"] ←ₛ getImpl st { name := "input" } 0 0)["out[0]"] ←ₛ
          getImpl (st["x"] ←ₛ getImpl st { name := "input" } 0 0) { name := "output" } 0 0)["andEqz x"] ←ₛ
        some
          (Lit.Constraint
            (Option.get!
                (State.props
                  ((st["x"] ←ₛ getImpl st { name := "input" } 0 0)["out[0]"] ←ₛ
                    getImpl (st["x"] ←ₛ getImpl st { name := "input" } 0 0) { name := "output" } 0 0)
                  { name := "true" }) ∧
              Option.get!
                  (State.felts
                    ((st["x"] ←ₛ getImpl st { name := "input" } 0 0)["out[0]"] ←ₛ
                      getImpl (st["x"] ←ₛ getImpl st { name := "input" } 0 0) { name := "output" } 0 0)
                    { name := "x" }) =
                0))

-- Run the whole program by using part₁_state rather than Code.part₁
def part₁_state_update (st: State): State :=
  Γ (part₁_state st) ⟦Code.part₂; Code.part₃; Code.part₄⟧

-- Prove that substituting part₁_state for Code.part₁ produces the same result
lemma part₁_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₁; Code.part₂; Code.part₃; Code.part₄) st) ↔
  Code.getReturn (part₁_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₂; Code.part₃; Code.part₄) = prog
  unfold Code.part₁
  MLIR
  unfold part₁_state_update part₁_state
  rewrite [←eq]
  rfl

lemma part₁_updates_opaque {st : State} : 
  Code.getReturn (part₀_state_update st) ↔
  Code.getReturn (part₁_state_update (part₀_state st)) := by
  simp [part₀_state_update, part₁_wp]

end Risc0.IsZero.Constraints.WP
