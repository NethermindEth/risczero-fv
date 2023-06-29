import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart12

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part13 on st
def part13_state (st: State) : State := 
  
        ((((st["%52"] ←ₛ getImpl st { name := "data" } 0 12)[felts][{ name := "%53" }] ←
              Option.get! (State.felts (st["%52"] ←ₛ getImpl st { name := "data" } 0 12) { name := "%52" }) *
                Option.get! (State.felts st { name := "%11" }))[felts][{ name := "%54" }] ←
            Option.get! (State.felts st { name := "%51" }) +
              Option.get! (State.felts (st["%52"] ←ₛ getImpl st { name := "data" } 0 12) { name := "%52" }) *
                Option.get! (State.felts st { name := "%11" }))["%55"] ←ₛ
          getImpl st { name := "data" } 0
            13) 

-- Run the whole program by using part13_state rather than Code.part13
def part13_state_update (st: State): State :=
  Γ (part13_state st) ⟦Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part13_state for Code.part13 produces the same result
lemma part13_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part13_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part13
  MLIR
  unfold part13_state_update part13_state
  rewrite [←eq]
  rfl

lemma part13_updates_opaque {st : State} : 
  Code.getReturn (part12_state_update st) ↔
  Code.getReturn (part13_state_update (part12_state st)) := by
  simp [part12_state_update, part13_wp]

end Risc0.OneHot20.Constraints.WP