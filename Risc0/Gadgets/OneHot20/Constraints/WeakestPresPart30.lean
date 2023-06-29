import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart29

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part30 on st
def part30_state (st: State) : State := 
  
        ((((st[props][{ name := "%120" }] ←
                (Option.get! (State.props st { name := "%116" }) ∧
                  Option.get! (State.felts st { name := "%119" }) = 0))[felts][{ name := "%121" }] ←
              Option.get! (State.felts st { name := "%117" }) +
                Option.get! (State.felts st { name := "%46" }))[felts][{ name := "%122" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%49" }))[felts][{ name := "%123" }] ←
          Option.get! (State.felts st { name := "%49" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%49" }))) 

-- Run the whole program by using part30_state rather than Code.part30
def part30_state_update (st: State): State :=
  Γ (part30_state st) ⟦Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part30_state for Code.part30 produces the same result
lemma part30_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part30_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part30
  MLIR
  unfold part30_state_update part30_state
  rewrite [←eq]
  rfl

lemma part30_updates_opaque {st : State} : 
  Code.getReturn (part29_state_update st) ↔
  Code.getReturn (part30_state_update (part29_state st)) := by
  simp [part29_state_update, part30_wp]

end Risc0.OneHot20.Constraints.WP