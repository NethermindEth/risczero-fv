import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart33

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part34 on st
def part34_state (st: State) : State := 
  
        ((((st[props][{ name := "%136" }] ←
                (Option.get! (State.props st { name := "%132" }) ∧
                  Option.get! (State.felts st { name := "%135" }) = 0))[felts][{ name := "%137" }] ←
              Option.get! (State.felts st { name := "%133" }) +
                Option.get! (State.felts st { name := "%58" }))[felts][{ name := "%138" }] ←
            Option.get!
                ((st.felts[{ name := "%137" }] ←ₘ
                    Option.get! (State.felts st { name := "%133" }) + Option.get! (State.felts st { name := "%58" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%137" }] ←ₘ
                    Option.get! (State.felts st { name := "%133" }) + Option.get! (State.felts st { name := "%58" }))
                  { name := "%61" }))[felts][{ name := "%139" }] ←
          Option.get!
              (((st.felts[{ name := "%137" }] ←ₘ
                    Option.get! (State.felts st { name := "%133" }) +
                      Option.get! (State.felts st { name := "%58" }))[{ name := "%138" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%137" }] ←ₘ
                          Option.get! (State.felts st { name := "%133" }) +
                            Option.get! (State.felts st { name := "%58" }))
                        { name := "%0" }) -
                    Option.get!
                      ((st.felts[{ name := "%137" }] ←ₘ
                          Option.get! (State.felts st { name := "%133" }) +
                            Option.get! (State.felts st { name := "%58" }))
                        { name := "%61" }))
                { name := "%61" }) *
            (Option.get!
                ((st.felts[{ name := "%137" }] ←ₘ
                    Option.get! (State.felts st { name := "%133" }) + Option.get! (State.felts st { name := "%58" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%137" }] ←ₘ
                    Option.get! (State.felts st { name := "%133" }) + Option.get! (State.felts st { name := "%58" }))
                  { name := "%61" }))) 

-- Run the whole program by using part34_state rather than Code.part34
def part34_state_update (st: State): State :=
  Γ (part34_state st) ⟦Code.part35; Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part34_state for Code.part34 produces the same result
lemma part34_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part34; Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part34_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part34
  MLIR
  unfold part34_state_update part34_state
  rewrite [←eq]
  rfl

lemma part34_updates_opaque {st : State} : 
  Code.getReturn (part33_state_update st) ↔
  Code.getReturn (part34_state_update (part33_state st)) := by
  simp [part33_state_update, part34_wp]

end Risc0.OneHot20.Constraints.WP