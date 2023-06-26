import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart19

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part20 on st
def part20_state (st: State) : State := 
  
        ((((st[felts][{ name := "%80" }] ←
                Option.get! (State.felts st { name := "%78" }) *
                  Option.get! (State.felts st { name := "%79" }))[props][{ name := "%81" }] ←
              (Option.get! (State.props st { name := "%77" }) ∧
                (Option.get! (State.felts st { name := "%78" }) = 0 ∨
                  Option.get! (State.felts st { name := "%79" }) = 0)))[felts][{ name := "%82" }] ←
            Option.get!
                ((st.felts[{ name := "%80" }] ←ₘ
                    Option.get! (State.felts st { name := "%78" }) * Option.get! (State.felts st { name := "%79" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%80" }] ←ₘ
                    Option.get! (State.felts st { name := "%78" }) * Option.get! (State.felts st { name := "%79" }))
                  { name := "%21" }))[felts][{ name := "%83" }] ←
          Option.get!
              (((st.felts[{ name := "%80" }] ←ₘ
                    Option.get! (State.felts st { name := "%78" }) *
                      Option.get! (State.felts st { name := "%79" }))[{ name := "%82" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%80" }] ←ₘ
                          Option.get! (State.felts st { name := "%78" }) *
                            Option.get! (State.felts st { name := "%79" }))
                        { name := "%0" }) -
                    Option.get!
                      ((st.felts[{ name := "%80" }] ←ₘ
                          Option.get! (State.felts st { name := "%78" }) *
                            Option.get! (State.felts st { name := "%79" }))
                        { name := "%21" }))
                { name := "%21" }) *
            (Option.get!
                ((st.felts[{ name := "%80" }] ←ₘ
                    Option.get! (State.felts st { name := "%78" }) * Option.get! (State.felts st { name := "%79" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%80" }] ←ₘ
                    Option.get! (State.felts st { name := "%78" }) * Option.get! (State.felts st { name := "%79" }))
                  {
                    name :=
                      "%21" }))) 

-- Run the whole program by using part20_state rather than Code.part20
def part20_state_update (st: State): State :=
  Γ (part20_state st) ⟦Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part20_state for Code.part20 produces the same result
lemma part20_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part20; Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part20_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part21; Code.part22; Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part20
  MLIR
  unfold part20_state_update part20_state
  rewrite [←eq]
  rfl

lemma part20_updates_opaque {st : State} : 
  Code.getReturn (part19_state_update st) ↔
  Code.getReturn (part20_state_update (part19_state st)) := by
  simp [part19_state_update, part20_wp]

end Risc0.OneHot20.Constraints.WP