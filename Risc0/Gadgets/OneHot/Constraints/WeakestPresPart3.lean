import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart2

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₃ on st
def part₃_state (st: State) : State :=
  ((((st[felts][{ name := "2*output[2]+output[1]-input" }] ←
              Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                Option.get!
                  (State.felts st { name := "input" }))[props][{ name := "andEqz 2*output[2]+output[1]-input" }] ←
            (Option.get! (State.props st { name := "true" }) ∧
              Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                  Option.get! (State.felts st { name := "input" }) =
                0))["output[0]"] ←ₛ
          getImpl st { name := "output" } 0 0)[felts][{ name := "1-Output[0]" }] ←
        Option.get!
            (State.felts
              (((st[felts][{ name := "2*output[2]+output[1]-input" }] ←
                    Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                      Option.get!
                        (State.felts st { name := "input" }))[props][{ name := "andEqz 2*output[2]+output[1]-input" }] ←
                  (Option.get! (State.props st { name := "true" }) ∧
                    Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                        Option.get! (State.felts st { name := "input" }) =
                      0))["output[0]"] ←ₛ
                getImpl st { name := "output" } 0 0)
              { name := "1" }) -
          Option.get!
            (State.felts
              (((st[felts][{ name := "2*output[2]+output[1]-input" }] ←
                    Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                      Option.get!
                        (State.felts st { name := "input" }))[props][{ name := "andEqz 2*output[2]+output[1]-input" }] ←
                  (Option.get! (State.props st { name := "true" }) ∧
                    Option.get! (State.felts st { name := "2*output[2]+output[1]" }) -
                        Option.get! (State.felts st { name := "input" }) =
                      0))["output[0]"] ←ₛ
                getImpl st { name := "output" } 0 0)
              { name := "output[0]" }))

-- Run the whole program by using part₃_state rather than Code.part₃
def part₃_state_update (st: State): State :=
  Γ (part₃_state st) ⟦Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₃_state for Code.part₃ produces the same result
lemma part₃_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₃; Code.part₄; Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₃_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₃
  MLIR
  unfold part₃_state_update part₃_state
  rewrite [←eq]
  rfl

lemma part₃_updates_opaque {st : State} : 
  Code.getReturn (part₂_state_update st) ↔
  Code.getReturn (part₃_state_update (part₂_state st)) := by
  simp [part₂_state_update, part₃_wp]

end Risc0.OneHot.Constraints.WP
