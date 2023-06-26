import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart36

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part37 on st
def part37_state (st: State) : State := 
  
        ((((st[props][{ name := "%148" }] ←
                (Option.get! (State.props st { name := "%144" }) ∧
                  Option.get! (State.felts st { name := "%147" }) = 0))[felts][{ name := "%149" }] ←
              Option.get! (State.felts st { name := "%145" }) +
                Option.get! (State.felts st { name := "%67" }))[felts][{ name := "%150" }] ←
            Option.get!
                ((st.felts[{ name := "%149" }] ←ₘ
                    Option.get! (State.felts st { name := "%145" }) + Option.get! (State.felts st { name := "%67" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%149" }] ←ₘ
                    Option.get! (State.felts st { name := "%145" }) + Option.get! (State.felts st { name := "%67" }))
                  { name := "%70" }))[felts][{ name := "%151" }] ←
          Option.get!
              (((st.felts[{ name := "%149" }] ←ₘ
                    Option.get! (State.felts st { name := "%145" }) +
                      Option.get! (State.felts st { name := "%67" }))[{ name := "%150" }] ←ₘ
                  Option.get!
                      ((st.felts[{ name := "%149" }] ←ₘ
                          Option.get! (State.felts st { name := "%145" }) +
                            Option.get! (State.felts st { name := "%67" }))
                        { name := "%0" }) -
                    Option.get!
                      ((st.felts[{ name := "%149" }] ←ₘ
                          Option.get! (State.felts st { name := "%145" }) +
                            Option.get! (State.felts st { name := "%67" }))
                        { name := "%70" }))
                { name := "%70" }) *
            (Option.get!
                ((st.felts[{ name := "%149" }] ←ₘ
                    Option.get! (State.felts st { name := "%145" }) + Option.get! (State.felts st { name := "%67" }))
                  { name := "%0" }) -
              Option.get!
                ((st.felts[{ name := "%149" }] ←ₘ
                    Option.get! (State.felts st { name := "%145" }) + Option.get! (State.felts st { name := "%67" }))
                  { name := "%70" }))) 

-- Run the whole program by using part37_state rather than Code.part37
def part37_state_update (st: State): State :=
  Γ (part37_state st) ⟦Code.part38; Code.part39⟧

-- Prove that substituting part37_state for Code.part37 produces the same result
lemma part37_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part37; Code.part38; Code.part39) st) ↔
  Code.getReturn (part37_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part38; Code.part39) = prog
  unfold Code.part37
  MLIR
  unfold part37_state_update part37_state
  rewrite [←eq]
  rfl

lemma part37_updates_opaque {st : State} : 
  Code.getReturn (part36_state_update st) ↔
  Code.getReturn (part37_state_update (part36_state st)) := by
  simp [part36_state_update, part37_wp]

end Risc0.OneHot20.Constraints.WP