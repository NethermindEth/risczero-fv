import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart6

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part7 on st
def part7_state (st: State) : State := 
  
        ((((st["%28"] ←ₛ getImpl st { name := "data" } 0 4)[felts][{ name := "%29" }] ←
              Option.get! (State.felts (st["%28"] ←ₛ getImpl st { name := "data" } 0 4) { name := "%28" }) *
                Option.get!
                  (State.felts (st["%28"] ←ₛ getImpl st { name := "data" } 0 4)
                    { name := "%3" }))[felts][{ name := "%30" }] ←
            Option.get!
                (((st["%28"] ←ₛ getImpl st { name := "data" } 0 4).felts[{ name := "%29" }] ←ₘ
                    Option.get! (State.felts (st["%28"] ←ₛ getImpl st { name := "data" } 0 4) { name := "%28" }) *
                      Option.get! (State.felts (st["%28"] ←ₛ getImpl st { name := "data" } 0 4) { name := "%3" }))
                  { name := "%27" }) +
              Option.get! (State.felts (st["%28"] ←ₛ getImpl st { name := "data" } 0 4) { name := "%28" }) *
                Option.get! (State.felts (st["%28"] ←ₛ getImpl st { name := "data" } 0 4) { name := "%3" }))["%31"] ←ₛ
          getImpl (st["%28"] ←ₛ getImpl st { name := "data" } 0 4) { name := "data" } 0
            5) 

-- Run the whole program by using part7_state rather than Code.part7
def part7_state_update (st: State): State :=
  Γ (part7_state st) ⟦Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part7_state for Code.part7 produces the same result
lemma part7_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part7_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part7
  MLIR
  unfold part7_state_update part7_state
  rewrite [←eq]
  rfl

lemma part7_updates_opaque {st : State} : 
  Code.getReturn (part6_state_update st) ↔
  Code.getReturn (part7_state_update (part6_state st)) := by
  simp [part6_state_update, part7_wp]

end Risc0.OneHot20.Constraints.WP