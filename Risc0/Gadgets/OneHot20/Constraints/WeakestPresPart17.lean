import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart16

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part17 on st
def part17_state (st: State) : State := 
  
        ((((st[felts][{ name := "%68" }] ←
                Option.get! (State.felts st { name := "%67" }) *
                  Option.get! (State.felts st { name := "%16" }))[felts][{ name := "%69" }] ←
              Option.get!
                  ((st.felts[{ name := "%68" }] ←ₘ
                      Option.get! (State.felts st { name := "%67" }) * Option.get! (State.felts st { name := "%16" }))
                    { name := "%66" }) +
                Option.get! (State.felts st { name := "%67" }) *
                  Option.get! (State.felts st { name := "%16" }))["%70"] ←ₛ
            getImpl st { name := "data" } 0 18)[felts][{ name := "%71" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%68" }] ←
                      Option.get! (State.felts st { name := "%67" }) *
                        Option.get! (State.felts st { name := "%16" }))[felts][{ name := "%69" }] ←
                    Option.get!
                        ((st.felts[{ name := "%68" }] ←ₘ
                            Option.get! (State.felts st { name := "%67" }) *
                              Option.get! (State.felts st { name := "%16" }))
                          { name := "%66" }) +
                      Option.get! (State.felts st { name := "%67" }) *
                        Option.get! (State.felts st { name := "%16" }))["%70"] ←ₛ
                  getImpl st { name := "data" } 0 18)
                { name := "%70" }) *
            Option.get!
              (State.felts
                (((st[felts][{ name := "%68" }] ←
                      Option.get! (State.felts st { name := "%67" }) *
                        Option.get! (State.felts st { name := "%16" }))[felts][{ name := "%69" }] ←
                    Option.get!
                        ((st.felts[{ name := "%68" }] ←ₘ
                            Option.get! (State.felts st { name := "%67" }) *
                              Option.get! (State.felts st { name := "%16" }))
                          { name := "%66" }) +
                      Option.get! (State.felts st { name := "%67" }) *
                        Option.get! (State.felts st { name := "%16" }))["%70"] ←ₛ
                  getImpl st { name := "data" } 0 18)
                {
                  name :=
                    "%17" })) 

-- Run the whole program by using part17_state rather than Code.part17
def part17_state_update (st: State): State :=
  Γ (part17_state st) ⟦Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part17_state for Code.part17 produces the same result
lemma part17_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part17_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part17
  MLIR
  unfold part17_state_update part17_state
  rewrite [←eq]
  rfl

lemma part17_updates_opaque {st : State} : 
  Code.getReturn (part16_state_update st) ↔
  Code.getReturn (part17_state_update (part16_state st)) := by
  simp [part16_state_update, part17_wp]

end Risc0.OneHot20.Constraints.WP