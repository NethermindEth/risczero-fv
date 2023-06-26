import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart10

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part11 on st
def part11_state (st: State) : State := 
  
        ((((st[felts][{ name := "%44" }] ←
                Option.get! (State.felts st { name := "%43" }) *
                  Option.get! (State.felts st { name := "%8" }))[felts][{ name := "%45" }] ←
              Option.get! (State.felts st { name := "%42" }) +
                Option.get! (State.felts st { name := "%43" }) *
                  Option.get! (State.felts st { name := "%8" }))["%46"] ←ₛ
            getImpl st { name := "data" } 0 10)[felts][{ name := "%47" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%44" }] ←
                      Option.get! (State.felts st { name := "%43" }) *
                        Option.get! (State.felts st { name := "%8" }))[felts][{ name := "%45" }] ←
                    Option.get! (State.felts st { name := "%42" }) +
                      Option.get! (State.felts st { name := "%43" }) *
                        Option.get! (State.felts st { name := "%8" }))["%46"] ←ₛ
                  getImpl st { name := "data" } 0 10)
                { name := "%46" }) *
            Option.get!
              (State.felts st
                {
                  name :=
                    "%9" })) 

-- Run the whole program by using part11_state rather than Code.part11
def part11_state_update (st: State): State :=
  Γ (part11_state st) ⟦Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part11_state for Code.part11 produces the same result
lemma part11_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part11; Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part11_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part12; Code.part13; Code.part14; Code.part15; Code.part16; Code.part17; Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part11
  MLIR
  unfold part11_state_update part11_state
  rewrite [←eq]
  rfl

lemma part11_updates_opaque {st : State} : 
  Code.getReturn (part10_state_update st) ↔
  Code.getReturn (part11_state_update (part10_state st)) := by
  simp [part10_state_update, part11_wp]

end Risc0.OneHot20.Constraints.WP