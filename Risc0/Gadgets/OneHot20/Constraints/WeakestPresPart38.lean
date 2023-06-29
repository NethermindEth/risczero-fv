import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Constraints.Code
import Risc0.Gadgets.OneHot20.Constraints.WeakestPresPart37

namespace Risc0.OneHot20.Constraints.WP

open MLIRNotation

-- The state obtained by running Code.part38 on st
def part38_state (st: State) : State := 
  
        ((((st[props][{ name := "%152" }] ←
                (Option.get! (State.props st { name := "%148" }) ∧
                  Option.get! (State.felts st { name := "%151" }) = 0))[felts][{ name := "%153" }] ←
              Option.get! (State.felts st { name := "%149" }) +
                Option.get! (State.felts st { name := "%70" }))[felts][{ name := "%154" }] ←
            Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%73" }))[felts][{ name := "%155" }] ←
          Option.get! (State.felts st { name := "%73" }) *
            (Option.get! (State.felts st { name := "%0" }) -
              Option.get! (State.felts st { name := "%73" }))) 

-- Run the whole program by using part38_state rather than Code.part38
def part38_state_update (st: State): State :=
  Γ (part38_state st) ⟦Code.part39⟧

-- Prove that substituting part38_state for Code.part38 produces the same result
lemma part38_wp {st : State} :
  Code.getReturn (MLIR.runProgram (Code.part38; Code.part39) st) ↔
  Code.getReturn (part38_state_update st) := by
  unfold MLIR.runProgram; simp only
  generalize eq : (Code.part39) = prog
  unfold Code.part38
  MLIR
  unfold part38_state_update part38_state
  rewrite [←eq]
  rfl

lemma part38_updates_opaque {st : State} : 
  Code.getReturn (part37_state_update st) ↔
  Code.getReturn (part38_state_update (part37_state st)) := by
  simp [part37_state_update, part38_wp]

end Risc0.OneHot20.Constraints.WP