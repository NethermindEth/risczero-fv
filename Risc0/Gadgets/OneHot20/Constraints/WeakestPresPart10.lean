import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart9

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part10 on st
def part10_state (st: State) : State := 
  
        ((((st["%40"] ←ₛ getImpl st { name := "data" } 0 8)[felts][{ name := "%41" }] ←
              Option.get! (State.felts (st["%40"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%40" }) *
                Option.get!
                  (State.felts (st["%40"] ←ₛ getImpl st { name := "data" } 0 8)
                    { name := "%7" }))[felts][{ name := "%42" }] ←
            Option.get!
                (((st["%40"] ←ₛ getImpl st { name := "data" } 0 8).felts[{ name := "%41" }] ←ₘ
                    Option.get! (State.felts (st["%40"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%40" }) *
                      Option.get! (State.felts (st["%40"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%7" }))
                  { name := "%39" }) +
              Option.get! (State.felts (st["%40"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%40" }) *
                Option.get! (State.felts (st["%40"] ←ₛ getImpl st { name := "data" } 0 8) { name := "%7" }))["%43"] ←ₛ
          getImpl (st["%40"] ←ₛ getImpl st { name := "data" } 0 8) { name := "data" } 0
            9) 

-- Run the whole program by using part10_state rather than Code.part10
def part10_state_update (st: State): State :=
  Γ (part10_state st) ⟦Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part10_state for Code.part10 produces the same result
lemma part10_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part10_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part10
  MLIR
  unfold part10_state_update part10_state
  rewrite [←eq]
  rfl

lemma part10_updates_opaque {st : State} : 
  Code.getReturn (part9_state_update st) ↔
  Code.getReturn (part10_state_update (part9_state st)) := by
  simp [part9_state_update, part10_wp]

end Risc0.OneHot20.Constraints.WP