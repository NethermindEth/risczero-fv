import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart24

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part25 on st
def part25_state (st: State) : State := 
  
        ((((st[props][{ name := "%100" }] ←
                (Option.get! (State.props st { name := "%96" }) ∧
                  Option.get! (State.felts st { name := "%99" }) = 0))[felts][{ name := "%101" }] ←
              Option.get! (State.felts st { name := "%97" }) +
                Option.get! (State.felts st { name := "%31" }))[felts][{ name := "%102" }] ←
            Option.get!
                ((st.felts[{ name := "%101" }] ←ₘ
                    Option.get! (State.felts st { name := "%97" }) + Option.get! (State.felts st { name := "%31" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%101" }] ←ₘ
                    Option.get! (State.felts st { name := "%97" }) + Option.get! (State.felts st { name := "%31" }))
                  { name := "%34" }))[felts][{ name := "%103" }] ←
          Option.get!
              (((st.felts[{ name := "%101" }] ←ₘ
                    Option.get! (State.felts st { name := "%97" }) +
                      Option.get! (State.felts st { name := "%31" }))[{ name := "%102" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%101" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%31" }))
                        { name := "%0" }) -
                    Option.get!
                      ((st.felts[{ name := "%101" }] ←ₘ
                          Option.get! (State.felts st { name := "%97" }) +
                            Option.get! (State.felts st { name := "%31" }))
                        { name := "%34" }))
                { name := "%34" }) *
            (Option.get!
                ((st.felts[{ name := "%101" }] ←ₘ
                    Option.get! (State.felts st { name := "%97" }) + Option.get! (State.felts st { name := "%31" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%101" }] ←ₘ
                    Option.get! (State.felts st { name := "%97" }) + Option.get! (State.felts st { name := "%31" }))
                  {
                    name :=
                      "%34" }))) 

-- Run the whole program by using part25_state rather than Code.part25
def part25_state_update (st: State): State :=
  Γ (part25_state st) ⟦Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part25_state for Code.part25 produces the same result
lemma part25_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part25_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part25
  MLIR
  unfold part25_state_update part25_state
  rewrite [←eq]
  rfl

lemma part25_updates_opaque {st : State} : 
  Code.getReturn (part24_state_update st) ↔
  Code.getReturn (part25_state_update (part24_state st)) := by
  simp [part24_state_update, part25_wp]

end Risc0.OneHot20.Constraints.WP