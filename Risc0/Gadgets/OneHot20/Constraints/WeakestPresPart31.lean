import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart30

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part31 on st
def part31_state (st: State) : State := 
  
        ((((st[props][{ name := "%124" }] ←
                (Option.get! (State.props st { name := "%120" }) ∧
                  Option.get! (State.felts st { name := "%123" }) = 0))[felts][{ name := "%125" }] ←
              Option.get! (State.felts st { name := "%121" }) +
                Option.get! (State.felts st { name := "%49" }))[felts][{ name := "%126" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%52" }))[felts][{ name := "%127" }] ←
          Option.get! (State.felts st { name := "%52" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%52" }))) 

-- Run the whole program by using part31_state rather than Code.part31
def part31_state_update (st: State): State :=
  Γ (part31_state st) ⟦Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part31_state for Code.part31 produces the same result
lemma part31_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part31_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part31
  MLIR
  unfold part31_state_update part31_state
  rewrite [←eq]
  rfl

lemma part31_updates_opaque {st : State} : 
  Code.getReturn (part30_state_update st) ↔
  Code.getReturn (part31_state_update (part30_state st)) := by
  simp [part30_state_update, part31_wp]

end Risc0.OneHot20.Constraints.WP