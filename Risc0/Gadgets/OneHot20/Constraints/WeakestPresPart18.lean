import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart17

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part18 on st
def part18_state (st: State) : State := 
  
        ((((st[felts][{ name := "%72" }] ←
                Option.get! (State.felts st { name := "%69" }) +
                  Option.get! (State.felts st { name := "%71" }))["%73"] ←ₛ
              getImpl st { name := "data" } 0 19)[felts][{ name := "%74" }] ←
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%72" }] ←
                      Option.get! (State.felts st { name := "%69" }) +
                        Option.get! (State.felts st { name := "%71" }))["%73"] ←ₛ
                    getImpl st { name := "data" } 0 19)
                  { name := "%73" }) *
              Option.get! (State.felts st { name := "%18" }))[felts][{ name := "%75" }] ←
          Option.get! (State.felts st { name := "%69" }) + Option.get! (State.felts st { name := "%71" }) +
            Option.get!
                (State.felts
                  ((st[felts][{ name := "%72" }] ←
                      Option.get! (State.felts st { name := "%69" }) +
                        Option.get! (State.felts st { name := "%71" }))["%73"] ←ₛ
                    getImpl st { name := "data" } 0 19)
                  { name := "%73" }) *
              Option.get!
                (State.felts st
                  {
                    name :=
                      "%18" })) 

-- Run the whole program by using part18_state rather than Code.part18
def part18_state_update (st: State): State :=
  Γ (part18_state st) ⟦Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part18_state for Code.part18 produces the same result
lemma part18_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part18; Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part18_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part18
  MLIR
  unfold part18_state_update part18_state
  rewrite [←eq]
  rfl

lemma part18_updates_opaque {st : State} : 
  Code.getReturn (part17_state_update st) ↔
  Code.getReturn (part18_state_update (part17_state st)) := by
  simp [part17_state_update, part18_wp]

end Risc0.OneHot20.Constraints.WP