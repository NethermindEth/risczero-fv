import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart8

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part9 on st
def part9_state (st: State) : State := 
  
        ((((st[felts][{ name := "%36" }] ←
                Option.get! (State.felts st { name := "%33" }) +
                  Option.get! (State.felts st { name := "%35" }))["%37"] ←ₛ
              getImpl st { name := "data" } 0 7)[felts][{ name := "%38" }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%36" }] ←
                      Option.get! (State.felts st { name := "%33" }) +
                        Option.get! (State.felts st { name := "%35" }))["%37"] ←ₛ
                    getImpl st { name := "data" } 0 7)
                  { name := "%37" }) *
              Option.get! (State.felts st { name := "%6" }))[felts][{ name := "%39" }] ←
          Option.get! (State.felts st { name := "%33" }) + Option.get! (State.felts st { name := "%35" }) +
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%36" }] ←
                      Option.get! (State.felts st { name := "%33" }) +
                        Option.get! (State.felts st { name := "%35" }))["%37"] ←ₛ
                    getImpl st { name := "data" } 0 7)
                  { name := "%37" }) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%6" })) 

-- Run the whole program by using part9_state rather than Code.part9
def part9_state_update (st: State): State :=
  Γ (part9_state st) ⟦Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part9_state for Code.part9 produces the same result
lemma part9_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part9_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part9
  MLIR
  unfold part9_state_update part9_state
  rewrite [←eq]
  rfl

lemma part9_updates_opaque {st : State} : 
  Code.getReturn (part8_state_update st) ↔
  Code.getReturn (part9_state_update (part8_state st)) := by
  simp [part8_state_update, part9_wp]

end Risc0.OneHot20.Constraints.WP