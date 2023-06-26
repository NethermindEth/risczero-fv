import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart18

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part19 on st
def part19_state (st: State) : State := 
  
        ((((st[felts][{ name := "%76" }] ←
                Option.get! (State.felts st { name := "%75" }) -
                  Option.get! (State.felts st { name := "%20" }))[props][{ name := "%77" }] ←
              (Option.get! (State.props st { name := "%19" }) ∧
                Option.get! (State.felts st { name := "%75" }) - Option.get! (State.felts st { name := "%20" }) =
                  0))["%78"] ←ₛ
            getImpl st { name := "data" } 0 0)[felts][{ name := "%79" }] ←
          Option.get!
              (State.felts
                (((st[felts][{ name := "%76" }] ←
                      Option.get! (State.felts st { name := "%75" }) -
                        Option.get! (State.felts st { name := "%20" }))[props][{ name := "%77" }] ←
                    (Option.get! (State.props st { name := "%19" }) ∧
                      Option.get! (State.felts st { name := "%75" }) - Option.get! (State.felts st { name := "%20" }) =
                        0))["%78"] ←ₛ
                  getImpl st { name := "data" } 0 0)
                { name := "%0" }) -
            Option.get!
              (State.felts
                (((st[felts][{ name := "%76" }] ←
                      Option.get! (State.felts st { name := "%75" }) -
                        Option.get! (State.felts st { name := "%20" }))[props][{ name := "%77" }] ←
                    (Option.get! (State.props st { name := "%19" }) ∧
                      Option.get! (State.felts st { name := "%75" }) - Option.get! (State.felts st { name := "%20" }) =
                        0))["%78"] ←ₛ
                  getImpl st { name := "data" } 0 0)
                {
                  name :=
                    "%78" })) 

-- Run the whole program by using part19_state rather than Code.part19
def part19_state_update (st: State): State :=
  Γ (part19_state st) ⟦Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part19_state for Code.part19 produces the same result
lemma part19_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part19; Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part19_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part19
  MLIR
  unfold part19_state_update part19_state
  rewrite [←eq]
  rfl

lemma part19_updates_opaque {st : State} : 
  Code.getReturn (part18_state_update st) ↔
  Code.getReturn (part19_state_update (part18_state st)) := by
  simp [part18_state_update, part19_wp]

end Risc0.OneHot20.Constraints.WP