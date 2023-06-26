import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart7

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part8 on st
def part8_state (st: State) : State := 
  
        ((((st[felts][{ name := "%32" }] ←
                Option.get! (State.felts st { name := "%31" }) *
                  Option.get! (State.felts st { name := "%4" }))[felts][{ name := "%33" }] ←
              Option.get!
                  ((st.felts[{ name := "%32" }] ←ₘ
                      Option.get! (State.felts st { name := "%31" }) * Option.get! (State.felts st { name := "%4" }))
                    { name := "%30" }) +
                Option.get! (State.felts st { name := "%31" }) *
                  Option.get! (State.felts st { name := "%4" }))["%34"] ←ₛ
            getImpl st { name := "data" } 0 6)[felts][{ name := "%35" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%32" }] ←
                      Option.get! (State.felts st { name := "%31" }) *
                        Option.get! (State.felts st { name := "%4" }))[felts][{ name := "%33" }] ←
                    Option.get!
                        ((st.felts[{ name := "%32" }] ←ₘ
                            Option.get! (State.felts st { name := "%31" }) *
                              Option.get! (State.felts st { name := "%4" }))
                          { name := "%30" }) +
                      Option.get! (State.felts st { name := "%31" }) *
                        Option.get! (State.felts st { name := "%4" }))["%34"] ←ₛ
                  getImpl st { name := "data" } 0 6)
                { name := "%34" }) *
            Option.get!
              (State.felts
                (((st[felts][{ name := "%32" }] ←
                      Option.get! (State.felts st { name := "%31" }) *
                        Option.get! (State.felts st { name := "%4" }))[felts][{ name := "%33" }] ←
                    Option.get!
                        ((st.felts[{ name := "%32" }] ←ₘ
                            Option.get! (State.felts st { name := "%31" }) *
                              Option.get! (State.felts st { name := "%4" }))
                          { name := "%30" }) +
                      Option.get! (State.felts st { name := "%31" }) *
                        Option.get! (State.felts st { name := "%4" }))["%34"] ←ₛ
                  getImpl st { name := "data" } 0 6)
                {
                  name :=
                    "%5" })) 

-- Run the whole program by using part8_state rather than Code.part8
def part8_state_update (st: State): State :=
  Γ (part8_state st) ⟦Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part8_state for Code.part8 produces the same result
lemma part8_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part8; Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part8_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part9; Code.part10; Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part8
  MLIR
  unfold part8_state_update part8_state
  rewrite [←eq]
  rfl

lemma part8_updates_opaque {st : State} : 
  Code.getReturn (part7_state_update st) ↔
  Code.getReturn (part8_state_update (part7_state st)) := by
  simp [part7_state_update, part8_wp]

end Risc0.OneHot20.Constraints.WP