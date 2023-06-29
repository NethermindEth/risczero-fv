import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart35

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part36 on st
def part36_state (st: State) : State := 
  
        ((((st[props][{ name := "%144" }] ←
                (Option.get! (State.props st { name := "%140" }) ∧
                  Option.get! (State.felts st { name := "%143" }) = 0))[felts][{ name := "%145" }] ←
              Option.get! (State.felts st { name := "%141" }) +
                Option.get! (State.felts st { name := "%64" }))[felts][{ name := "%146" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%67" }))[felts][{ name := "%147" }] ←
          Option.get! (State.felts st { name := "%67" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%67" }))) 

-- Run the whole program by using part36_state rather than Code.part36
def part36_state_update (st: State): State :=
  Γ (part36_state st) ⟦Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part36_state for Code.part36 produces the same result
lemma part36_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part36_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part36
  MLIR
  unfold part36_state_update part36_state
  rewrite [←eq]
  rfl

lemma part36_updates_opaque {st : State} : 
  Code.getReturn (part35_state_update st) ↔
  Code.getReturn (part36_state_update (part35_state st)) := by
  simp [part35_state_update, part36_wp]

end Risc0.OneHot20.Constraints.WP