import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart32

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part33 on st
def part33_state (st: State) : State := 
  
        ((((st[props][{ name := "%132" }] ←
                (Option.get! (State.props st { name := "%128" }) ∧
                  Option.get! (State.felts st { name := "%131" }) = 0))[felts][{ name := "%133" }] ←
              Option.get! (State.felts st { name := "%129" }) +
                Option.get! (State.felts st { name := "%55" }))[felts][{ name := "%134" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%135" }] ←
          Option.get! (State.felts st { name := "%58" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  { name := "%58" }))) 

-- Run the whole program by using part33_state rather than Code.part33
def part33_state_update (st: State): State :=
  Γ (part33_state st) ⟦Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part33_state for Code.part33 produces the same result
lemma part33_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part33_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part33
  MLIR
  unfold part33_state_update part33_state
  rewrite [←eq]
  rfl

lemma part33_updates_opaque {st : State} : 
  Code.getReturn (part32_state_update st) ↔
  Code.getReturn (part33_state_update (part32_state st)) := by
  simp [part32_state_update, part33_wp]

end Risc0.OneHot20.Constraints.WP