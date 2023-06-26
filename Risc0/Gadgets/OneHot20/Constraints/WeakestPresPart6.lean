import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart5

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part6 on st
def part6_state (st: State) : State := 
  
        ((((st[felts][{ name := "%24" }] ←
                Option.get! (State.felts st { name := "%21" }) +
                  Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
              getImpl st { name := "data" } 0 3)[felts][{ name := "%26" }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%24" }] ←
                      Option.get! (State.felts st { name := "%21" }) +
                        Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                    getImpl st { name := "data" } 0 3)
                  { name := "%25" }) *
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%24" }] ←
                      Option.get! (State.felts st { name := "%21" }) +
                        Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                    getImpl st { name := "data" } 0 3)
                  { name := "%2" }))[felts][{ name := "%27" }] ←
          Option.get!
              ((((st[felts][{ name := "%24" }] ←
                        Option.get! (State.felts st { name := "%21" }) +
                          Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                      getImpl st { name := "data" } 0 3).felts[{ name := "%26" }] ←ₘ
                  Option.get!
                      (State.felts
                        ((st[felts][{ name := "%24" }] ←
                            Option.get! (State.felts st { name := "%21" }) +
                              Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                          getImpl st { name := "data" } 0 3)
                        { name := "%25" }) *
                    Option.get!
                      (State.felts
                        ((st[felts][{ name := "%24" }] ←
                            Option.get! (State.felts st { name := "%21" }) +
                              Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                          getImpl st { name := "data" } 0 3)
                        { name := "%2" }))
                { name := "%24" }) +
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%24" }] ←
                      Option.get! (State.felts st { name := "%21" }) +
                        Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                    getImpl st { name := "data" } 0 3)
                  { name := "%25" }) *
              Option.get!
                (State.felts
                  ((st[felts][{ name := "%24" }] ←
                      Option.get! (State.felts st { name := "%21" }) +
                        Option.get! (State.felts st { name := "%23" }))["%25"] ←ₛ
                    getImpl st { name := "data" } 0 3)
                  {
                    name :=
                      "%2" })) 

-- Run the whole program by using part6_state rather than Code.part6
def part6_state_update (st: State): State :=
  Γ (part6_state st) ⟦Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part6_state for Code.part6 produces the same result
lemma part6_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part6; Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part6_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part7; Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part6
  MLIR
  unfold part6_state_update part6_state
  rewrite [←eq]
  rfl

lemma part6_updates_opaque {st : State} : 
  Code.getReturn (part5_state_update st) ↔
  Code.getReturn (part6_state_update (part5_state st)) := by
  simp [part5_state_update, part6_wp]

end Risc0.OneHot20.Constraints.WP