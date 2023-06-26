import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart11

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part12 on st
def part12_state (st: State) : State := 
  
        ((((st[felts][{ name := "%48" }] ←
                Option.get! (State.felts st { name := "%45" }) +
                  Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
              getImpl st { name := "data" } 0 11)[felts][{ name := "%50" }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%48" }] ←
                      Option.get! (State.felts st { name := "%45" }) +
                        Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                    getImpl st { name := "data" } 0 11)
                  { name := "%49" }) *
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%48" }] ←
                      Option.get! (State.felts st { name := "%45" }) +
                        Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                    getImpl st { name := "data" } 0 11)
                  { name := "%10" }))[felts][{ name := "%51" }] ←
          Option.get!
              ((((st[felts][{ name := "%48" }] ←
                        Option.get! (State.felts st { name := "%45" }) +
                          Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                      getImpl st { name := "data" } 0 11).felts[{ name := "%50" }] ←ₘ
                  Option.get!
                      (State.felts
                        ((st[felts][{ name := "%48" }] ←
                            Option.get! (State.felts st { name := "%45" }) +
                              Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                          getImpl st { name := "data" } 0 11)
                        { name := "%49" }) *
                    Option.get!
                      (State.felts
                        ((st[felts][{ name := "%48" }] ←
                            Option.get! (State.felts st { name := "%45" }) +
                              Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                          getImpl st { name := "data" } 0 11)
                        { name := "%10" }))
                { name := "%48" }) +
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%48" }] ←
                      Option.get! (State.felts st { name := "%45" }) +
                        Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                    getImpl st { name := "data" } 0 11)
                  { name := "%49" }) *
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%48" }] ←
                      Option.get! (State.felts st { name := "%45" }) +
                        Option.get! (State.felts st { name := "%47" }))["%49"] ←ₛ
                    getImpl st { name := "data" } 0 11)
                  {
                    name :=
                      "%10" })) 

-- Run the whole program by using part12_state rather than Code.part12
def part12_state_update (st: State): State :=
  Γ (part12_state st) ⟦Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part12_state for Code.part12 produces the same result
lemma part12_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part12_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part12
  MLIR
  unfold part12_state_update part12_state
  rewrite [←eq]
  rfl

lemma part12_updates_opaque {st : State} : 
  Code.getReturn (part11_state_update st) ↔
  Code.getReturn (part12_state_update (part11_state st)) := by
  simp [part11_state_update, part12_wp]

end Risc0.OneHot20.Constraints.WP