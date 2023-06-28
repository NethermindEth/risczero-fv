import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart15

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part16 on st
def part16_state (st: State) : State := 
  
        ((((st["%64"] ←ₛ getImpl st { name := "data" } 0 16)[felts][{ name := "%65" }] ←
              Option.get! (State.felts (st["%64"] ←ₛ getImpl st { name := "data" } 0 16) { name := "%64" }) *
                Option.get! (State.felts st { name := "%15" }))[felts][{ name := "%66" }] ←
            Option.get! (State.felts st { name := "%63" }) +
              Option.get! (State.felts (st["%64"] ←ₛ getImpl st { name := "data" } 0 16) { name := "%64" }) *
                Option.get! (State.felts st { name := "%15" }))["%67"] ←ₛ
          getImpl st { name := "data" } 0
            17) 

-- Run the whole program by using part16_state rather than Code.part16
def part16_state_update (st: State): State :=
  Γ (part16_state st) ⟦Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part16_state for Code.part16 produces the same result
lemma part16_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part16_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part16
  MLIR
  unfold part16_state_update part16_state
  rewrite [←eq]
  rfl

lemma part16_updates_opaque {st : State} : 
  Code.getReturn (part15_state_update st) ↔
  Code.getReturn (part16_state_update (part15_state st)) := by
  simp [part15_state_update, part16_wp]

end Risc0.OneHot20.Constraints.WP