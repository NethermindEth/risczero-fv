import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart38

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part39 on st
def part39_state (st: State) : State := 
  
      ((((st[props][{ name := "%156" }] ←
              (Option.get! (State.props st { name := "%152" }) ∧
                Option.get! (State.felts st { name := "%155" }) = 0))[felts][{ name := "%157" }] ←
            Option.get! (State.felts st { name := "%153" }) +
              Option.get! (State.felts st { name := "%73" }))[felts][{ name := "%158" }] ←
          Option.get! (State.felts st { name := "%153" }) + Option.get! (State.felts st { name := "%73" }) -
            Option.get!
              ((st.felts[{ name := "%157" }] ←ₘ
                  Option.get! (State.felts st { name := "%153" }) + Option.get! (State.felts st { name := "%73" }))
                { name := "%0" }))[props][{ name := "%159" }] ←
        ((Option.get! (State.props st { name := "%152" }) ∧ Option.get! (State.felts st { name := "%155" }) = 0) ∧
          Option.get! (State.felts st { name := "%153" }) + Option.get! (State.felts st { name := "%73" }) -
              Option.get!
                ((st.felts[{ name := "%157" }] ←ₘ
                    Option.get! (State.felts st { name := "%153" }) + Option.get! (State.felts st { name := "%73" }))
                  { name := "%0" }) =
            0)) 

-- Prove that substituting part39_state for Code.part39 produces the same result
lemma part39_wp {st : State} :
  Code.getReturn (MLIR.runProgram Code.part39 st) ↔
  Code.getReturn (part39_state st) := by
  unfold MLIR.runProgram; simp only
  unfold Code.part39
  MLIR
  unfold part39_state
  rfl

lemma part39_updates_opaque {st : State} : 
  Code.getReturn (part38_state_update st) ↔
  Code.getReturn (part39_state (part38_state st)) := by
  simp [part38_state_update, part39_wp]

end Risc0.OneHot20.Constraints.WP