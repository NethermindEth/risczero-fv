import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart34

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part35 on st
def part35_state (st: State) : State := 
  
        ((((st[props][{ name := "%140" }] ←
                (Option.get! (State.props st { name := "%136" }) ∧
                  Option.get! (State.felts st { name := "%139" }) = 0))[felts][{ name := "%141" }] ←
              Option.get! (State.felts st { name := "%137" }) +
                Option.get! (State.felts st { name := "%61" }))[felts][{ name := "%142" }] ←
            Option.get!
                ((st.felts[{ name := "%141" }] ←ₘ
                    Option.get! (State.felts st { name := "%137" }) + Option.get! (State.felts st { name := "%61" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%141" }] ←ₘ
                    Option.get! (State.felts st { name := "%137" }) + Option.get! (State.felts st { name := "%61" }))
                  { name := "%64" }))[felts][{ name := "%143" }] ←
          Option.get!
              (((st.felts[{ name := "%141" }] ←ₘ
                    Option.get! (State.felts st { name := "%137" }) +
                      Option.get! (State.felts st { name := "%61" }))[{ name := "%142" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%141" }] ←ₘ
                          Option.get! (State.felts st { name := "%137" }) +
                            Option.get! (State.felts st { name := "%61" }))
                        { name := "%0" }) -
                    Option.get!
                      ((st.felts[{ name := "%141" }] ←ₘ
                          Option.get! (State.felts st { name := "%137" }) +
                            Option.get! (State.felts st { name := "%61" }))
                        { name := "%64" }))
                { name := "%64" }) *
            (Option.get!
                ((st.felts[{ name := "%141" }] ←ₘ
                    Option.get! (State.felts st { name := "%137" }) + Option.get! (State.felts st { name := "%61" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%141" }] ←ₘ
                    Option.get! (State.felts st { name := "%137" }) + Option.get! (State.felts st { name := "%61" }))
                  { name := "%64" }))) 

-- Run the whole program by using part35_state rather than Code.part35
def part35_state_update (st: State): State :=
  Γ (part35_state st) ⟦Code.part36; Code.part37; Code.part38; Code.part39⟧

-- Prove that substituting part35_state for Code.part35 produces the same result
lemma part35_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part35; Code.part36; Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part35_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part36; Code.part37; Code.part38; Code.part39) = prog
  unfold Code.part35
  MLIR
  unfold part35_state_update part35_state
  rewrite [←eq]
  rfl

lemma part35_updates_opaque {st : State} : 
  Code.getReturn (part34_state_update st) ↔
  Code.getReturn (part35_state_update (part34_state st)) := by
  simp [part34_state_update, part35_wp]

end Risc0.OneHot20.Constraints.WP