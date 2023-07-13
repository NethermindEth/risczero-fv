import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart4

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₅ on st
def part₅_state (st: State) : State :=
  ((((st[props][{ name := "andEqz output[1]<=1" }] ←
              (Option.get! (State.props st { name := "andEqz output[0]<=1" }) ∧
                Option.get! (State.felts st { name := "output[1]<=1" }) =
                  0))[felts][{ name := "output[0]+Output[1]" }] ←
            Option.get! (State.felts st { name := "output[0]" }) +
              Option.get! (State.felts st { name := "output[1]" }))[felts][{ name := "1-Output[2]" }] ←
          Option.get! (State.felts st { name := "1" }) -
            Option.get! (State.felts st { name := "output[2]" }))[felts][{ name := "output[2]<=1" }] ←
        Option.get! (State.felts st { name := "output[1]" }) *
          Option.get! (State.felts st { name := "1-Output[1]" }))

-- Run the whole program by using part₅_state rather than Code.part₅
def part₅_state_update (st: State): State :=
  Γ (part₅_state st) ⟦Code.part₆⟧

-- Prove that substituting part₅_state for Code.part₅ produces the same result
lemma part₅_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₅_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₆) = prog
  unfold Code.part₅
  MLIR
  unfold part₅_state_update part₅_state
  rewrite [←eq]
  rfl

lemma part₅_updates_opaque {st : State} : 
  Code.getReturn (part₄_state_update st) ↔
  Code.getReturn (part₅_state_update (part₄_state st)) := by
  simp [part₄_state_update, part₅_wp]

end Risc0.OneHot.Constraints.WP
