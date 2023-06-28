import Risc0.Basic
import Risc0.MlirTactics
import Risc0.Gadgets.OneHot20.Witness.Code
import Risc0.Gadgets.OneHot20.Witness.WeakestPresPart53

namespace Risc0.OneHot20.Witness.WP

open MLIRNotation

-- The state obtained by running Code.part54 on st
def part54_state (st: State) : State := 
  
        (withEqZero
          (Option.get! (State.felts st { name := "%133" }) + Option.get! (State.felts st { name := "%73" }) -
            Option.get! (State.felts st { name := "%18" }))
          ((st[felts][{ name := "%136" }] ←
              Option.get! (State.felts st { name := "%133" }) +
                Option.get! (State.felts st { name := "%73" }))[felts][{ name := "%137" }] ←
            Option.get! (State.felts st { name := "%133" }) + Option.get! (State.felts st { name := "%73" }) -
              Option.get! (State.felts st { name := "%18" }))) 

-- Prove that substituting part54_state for Code.part54 produces the same result
lemma part54_wp {st : State} {y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 y13 y14 y15 y16 y17 y18 y19 : Option Felt} :
  Code.getReturn (MLIR.runProgram Code.part54 st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part54_state st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  unfold MLIR.runProgram; simp only
  unfold Code.part54
  MLIR
  unfold part54_state
  rfl

lemma part54_updates_opaque {st : State} : 
  Code.getReturn (part53_state_update st) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] ↔
  Code.getReturn (part54_state (part53_state st)) = [y0, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17, y18, y19] := by
  simp [part53_state_update, part54_wp]

end Risc0.OneHot20.Witness.WP