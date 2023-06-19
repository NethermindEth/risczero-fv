import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot.Constraints.Code
import Risc0.Gadgets.OneHot.Constraints.WeakestPresPart1

namespace Risc0.OneHot.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part₂ on st
def part₂_state (st: State) : State :=
  (st[felts][{ name := "output[2]*2" }] ←
          Option.get! (State.felts st { name := "output[2]" }) *
            Option.get! (State.felts st { name := "2" }))[felts][{ name := "2*output[2]+output[1]" }] ←
        Option.get!
            ((st.felts[{ name := "output[2]*2" }] ←ₘ
                Option.get! (State.felts st { name := "output[2]" }) * Option.get! (State.felts st { name := "2" }))
              { name := "output[1]" }) +
          Option.get! (State.felts st { name := "output[2]" }) *
            Option.get! (State.felts st { name := "2" })

-- Run the whole program by using part₂_state rather than Code.part₂
def part₂_state_update (st: State): State :=
  Γ (part₂_state st) ⟦Code.part₃; Code.part₄; Code.part₅; Code.part₆⟧

-- Prove that substituting part₂_state for Code.part₂ produces the same result
lemma part₂_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part₂; Code.part₃; Code.part₄; Code.part₅; Code.part₆) st) ↔
  Code.getReturn (part₂_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part₃; Code.part₄; Code.part₅; Code.part₆) = prog
  unfold Code.part₂
  MLIR
  unfold part₂_state_update part₂_state
  rewrite [←eq]
  rfl

lemma part₂_updates_opaque {st : State} : 
  Code.getReturn (part₁_state_update st) ↔
  Code.getReturn (part₂_state_update (part₁_state st)) := by
  simp [part₁_state_update, part₂_wp]

end Risc0.OneHot.Constraints.WP
