import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart28

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part29 on st
def part29_state (st: State) : State := 
  
        ((((st[props][{ name := "%116" }] ←
                (Option.get! (State.props st { name := "%112" }) ∧
                  Option.get! (State.felts st { name := "%115" }) = 0))[felts][{ name := "%117" }] ←
              Option.get! (State.felts st { name := "%113" }) +
                Option.get! (State.felts st { name := "%43" }))[felts][{ name := "%118" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%46" }))[felts][{ name := "%119" }] ←
          Option.get! (State.felts st { name := "%46" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%46" }))) 

-- Run the whole program by using part29_state rather than Code.part29
def part29_state_update (st: State): State :=
  Γ (part29_state st) ⟦Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part29_state for Code.part29 produces the same result
lemma part29_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part29_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part29
  MLIR
  unfold part29_state_update part29_state
  rewrite [←eq]
  rfl

lemma part29_updates_opaque {st : State} : 
  Code.getReturn (part28_state_update st) ↔
  Code.getReturn (part29_state_update (part28_state st)) := by
  simp [part28_state_update, part29_wp]

end Risc0.OneHot20.Constraints.WP