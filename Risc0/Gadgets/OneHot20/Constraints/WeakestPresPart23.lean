import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart22

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part23 on st
def part23_state (st: State) : State := 
  
        ((((st[props][{ name := "%92" }] ←
                (Option.get! (State.props st { name := "%88" }) ∧
                  Option.get! (State.felts st { name := "%91" }) = 0))[felts][{ name := "%93" }] ←
              Option.get! (State.felts st { name := "%89" }) +
                Option.get! (State.felts st { name := "%25" }))[felts][{ name := "%94" }] ←
            Option.get!
                ((st.felts[{ name := "%93" }] ←ₘ
                    Option.get! (State.felts st { name := "%89" }) + Option.get! (State.felts st { name := "%25" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%93" }] ←ₘ
                    Option.get! (State.felts st { name := "%89" }) + Option.get! (State.felts st { name := "%25" }))
                  { name := "%28" }))[felts][{ name := "%95" }] ←
          Option.get!
              (((st.felts[{ name := "%93" }] ←ₘ
                    Option.get! (State.felts st { name := "%89" }) +
                      Option.get! (State.felts st { name := "%25" }))[{ name := "%94" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%93" }] ←ₘ
                          Option.get! (State.felts st { name := "%89" }) +
                            Option.get! (State.felts st { name := "%25" }))
                        { name := "%0" }) -
                    Option.get!
                      ((st.felts[{ name := "%93" }] ←ₘ
                          Option.get! (State.felts st { name := "%89" }) +
                            Option.get! (State.felts st { name := "%25" }))
                        { name := "%28" }))
                { name := "%28" }) *
            (Option.get!
                ((st.felts[{ name := "%93" }] ←ₘ
                    Option.get! (State.felts st { name := "%89" }) + Option.get! (State.felts st { name := "%25" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%93" }] ←ₘ
                    Option.get! (State.felts st { name := "%89" }) + Option.get! (State.felts st { name := "%25" }))
                  {
                    name :=
                      "%28" }))) 

-- Run the whole program by using part23_state rather than Code.part23
def part23_state_update (st: State): State :=
  Γ (part23_state st) ⟦Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part23_state for Code.part23 produces the same result
lemma part23_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part23; Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part23_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part24; Code.part25; Code.part26; Code.part27; Code.part28; Code.part29; Code.part30; Code.part31; Code.part32; Code.part33; Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part23
  MLIR
  unfold part23_state_update part23_state
  rewrite [←eq]
  rfl

lemma part23_updates_opaque {st : State} : 
  Code.getReturn (part22_state_update st) ↔
  Code.getReturn (part23_state_update (part22_state st)) := by
  simp [part22_state_update, part23_wp]

end Risc0.OneHot20.Constraints.WP