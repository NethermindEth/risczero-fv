import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart13

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part14 on st
def part14_state (st: State) : State := 
  
        ((((st[felts][{ name := "%56" }] ←
                Option.get! (State.felts st { name := "%55" }) *
                  Option.get! (State.felts st { name := "%12" }))[felts][{ name := "%57" }] ←
              Option.get!
                  ((st.felts[{ name := "%56" }] ←ₘ
                      Option.get! (State.felts st { name := "%55" }) * Option.get! (State.felts st { name := "%12" }))
                    { name := "%54" }) +
                Option.get! (State.felts st { name := "%55" }) *
                  Option.get! (State.felts st { name := "%12" }))["%58"] ←ₛ
            getImpl st { name := "data" } 0 14)[felts][{ name := "%59" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%56" }] ←
                      Option.get! (State.felts st { name := "%55" }) *
                        Option.get! (State.felts st { name := "%12" }))[felts][{ name := "%57" }] ←
                    Option.get!
                        ((st.felts[{ name := "%56" }] ←ₘ
                            Option.get! (State.felts st { name := "%55" }) *
                              Option.get! (State.felts st { name := "%12" }))
                          { name := "%54" }) +
                      Option.get! (State.felts st { name := "%55" }) *
                        Option.get! (State.felts st { name := "%12" }))["%58"] ←ₛ
                  getImpl st { name := "data" } 0 14)
                { name := "%58" }) *
            Option.get!
              (State.felts
                (((st[felts][{ name := "%56" }] ←
                      Option.get! (State.felts st { name := "%55" }) *
                        Option.get! (State.felts st { name := "%12" }))[felts][{ name := "%57" }] ←
                    Option.get!
                        ((st.felts[{ name := "%56" }] ←ₘ
                            Option.get! (State.felts st { name := "%55" }) *
                              Option.get! (State.felts st { name := "%12" }))
                          { name := "%54" }) +
                      Option.get! (State.felts st { name := "%55" }) *
                        Option.get! (State.felts st { name := "%12" }))["%58"] ←ₛ
                  getImpl st { name := "data" } 0 14)
                {
                  name :=
                    "%13" })) 

-- Run the whole program by using part14_state rather than Code.part14
def part14_state_update (st: State): State :=
  Γ (part14_state st) ⟦Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part14_state for Code.part14 produces the same result
lemma part14_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part14_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part14
  MLIR
  unfold part14_state_update part14_state
  rewrite [←eq]
  rfl

lemma part14_updates_opaque {st : State} : 
  Code.getReturn (part13_state_update st) ↔
  Code.getReturn (part14_state_update (part13_state st)) := by
  simp [part13_state_update, part14_wp]

end Risc0.OneHot20.Constraints.WP